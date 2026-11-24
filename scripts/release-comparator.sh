#!/usr/bin/env bash
# Release gate: run the toolchain's own `lake comparator` on every
# challenges/*/config.json and write an attestation report to comparator-report/.
# Used by .github/workflows/release-comparator.yml on a fresh GitHub-hosted Linux runner; also runs in a
# cloud worker session (as root) or on any Linux machine with sudo.
#
# Usage: scripts/release-comparator.sh install|run
#   install  make sure bubblewrap is present and unprivileged user namespaces are allowed
#   run      judge every challenge; exit 0 only if all pass
# Environment:
#   COMPARATOR_PARANOID=1|0   also run every external checker bundled with the toolchain (default 1)
#   COMPARATOR_WORKDIR=DIR    where to copy the repo when it sits under a home directory
#                             (default /srv/comparator-work)
#
# No external tool revisions: comparator, the exporter and the extra kernels ship with the toolchain in
# lean-toolchain, so the toolchain pin is the tool pin.
set -euo pipefail

ROOT=$(git rev-parse --show-toplevel)
REPORT="$ROOT/comparator-report"
PARANOID="${COMPARATOR_PARANOID:-1}"
SUDO=""; [ "$(id -u)" = 0 ] || SUDO=sudo

install() {
  mkdir -p "$REPORT/logs"
  if ! command -v bwrap >/dev/null; then
    $SUDO apt-get update -qq
    $SUDO apt-get install -y -qq bubblewrap
  fi
  # Ubuntu 24.04+ (hosted runners) restricts unprivileged user namespaces through AppArmor; bwrap needs them.
  local knob=/proc/sys/kernel/apparmor_restrict_unprivileged_userns
  if [ -e "$knob" ] && [ "$(cat "$knob")" != 0 ]; then
    $SUDO sysctl -w kernel.apparmor_restrict_unprivileged_userns=0
  fi
  bwrap --ro-bind / / --unshare-all true   # fails here, not mid-run, if the sandbox cannot start
  { bwrap --version; lake --version; } > "$REPORT/logs/tool-versions.txt" 2>&1
}

run() {
  mkdir -p "$REPORT/logs"
  # bwrap hides the home directories inside the sandbox, and challenge workspaces reach the root through
  # relative paths (`path = "../.."`, `packagesDir`). A repo under a home directory is judged from a copy.
  local work="$ROOT"
  case "$ROOT/" in
    /home/*|/root/*)
      work="${COMPARATOR_WORKDIR:-/srv/comparator-work}/$(basename "$ROOT")"
      $SUDO mkdir -p "$(dirname "$work")"
      $SUDO rm -rf "$work"
      $SUDO chown "$(id -u):$(id -g)" "$(dirname "$work")"
      echo "Copying $ROOT to $work (outside the home directories, for the sandbox)"
      cp -a "$ROOT" "$work"
      ;;
  esac
  python3 - "$ROOT" "$work" "$REPORT" "$PARANOID" <<'PY'
import json, pathlib, subprocess, sys
root, work, report = map(pathlib.Path, sys.argv[1:4])
paranoid = sys.argv[4] == '1'
def out(*args, cwd=root): return subprocess.check_output(args, cwd=cwd, text=True).strip()
# The workflow validates this inventory against formalization.yaml
# (scripts/check-formalization-manifest.rb --metadata-only) before this runs.
configs = sorted(work.glob('challenges/*/config.json'))
if not configs:
    raise SystemExit('No challenge configurations found')
manifest = json.loads((root / 'lake-manifest.json').read_text())
data = {
    'commit': out('git', 'rev-parse', 'HEAD'),
    'tree': out('git', 'rev-parse', 'HEAD^{tree}'),
    'lean_toolchain': (root / 'lean-toolchain').read_text().strip(),
    'lean_version': out('lean', '--version'),
    'mathlib_revision': next(p['rev'] for p in manifest['packages'] if p['name'] == 'mathlib'),
    'tools': {'engine': 'lake comparator', 'lake_version': out('lake', '--version'),
              'bwrap_version': out('bwrap', '--version'), 'paranoid': paranoid},
    'sandbox_note': (
        "Each challenge is judged by the toolchain's `lake comparator`. It evaluates the challenge "
        "workspace's configuration and builds and exports its code inside a bwrap sandbox: `/` read-only, "
        "home directories hidden, only `.lake` writable, and no network except for dependency resolution. "
        "Lake never loads the project's .olean files into its own process. "
        + ("Besides Lean's kernel, every external checker bundled with the toolchain (--paranoid) must "
           "accept the solution. " if paranoid else "Lean's default kernel is the only checker. ")
        + "Before the sandboxed run, the workflow downloads the Mathlib cache and builds the trusted library "
        "and the trusted Challenge targets outside the sandbox."),
    'results': [],
}
def write(): (report / 'attestation.json').write_text(json.dumps(data, indent=2) + '\n')
write()
failed = False
for config in configs:
    cfg = json.loads(config.read_text())
    if sorted(cfg['permitted_axioms']) != ['Classical.choice', 'Quot.sound', 'propext']:
        raise SystemExit(f'Unexpected axiom allowance in {config.relative_to(work)}')
    name = config.parent.name
    # A workspace without its own lakefile is built by the root lakefile (root-project workspace).
    has_lakefile = any((config.parent / f).exists() for f in ('lakefile.toml', 'lakefile.lean'))
    cmd = ['lake', 'comparator', f'--config={config}'] + (['--paranoid'] if paranoid else [])
    with (report / 'logs' / f'{name}.log').open('w') as log:
        log.write('$ ' + ' '.join(cmd) + '\n'); log.flush()
        result = subprocess.run(cmd, cwd=config.parent if has_lakefile else work,
                                stdout=log, stderr=subprocess.STDOUT)
    ok = result.returncode == 0
    data['results'].append({
        'config': str(config.relative_to(work)), 'theorems': cfg['theorem_names'],
        'permitted_axioms': cfg['permitted_axioms'],
        'axiom_check': 'passed' if ok else 'failed', 'exit_code': result.returncode,
        'result': 'PASS' if ok else ('FAIL' if result.returncode == 1 else 'ERROR'),
        'log': f'logs/{name}.log'})
    write()
    failed |= not ok
    print(f'{name}: {data["results"][-1]["result"]}', flush=True)
data['overall_result'] = 'FAIL' if failed else 'PASS'
write()
sys.exit(1 if failed else 0)
PY
}

case "${1:-}" in
  install) install ;;
  run) run ;;
  *) echo "usage: $0 install|run" >&2; exit 2 ;;
esac
