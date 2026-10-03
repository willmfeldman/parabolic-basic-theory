#!/usr/bin/env sh
# Build the standalone comparator workspaces from a fixed, reviewed list.
#
# `--challenge-only` is appropriate before a Comparator release run: it never
# elaborates untrusted Solution.lean files. `--trusted-all` is for local
# development after the whole checkout is trusted.
set -eu

usage() {
  cat <<'EOF'
Usage: scripts/build-challenges.sh --challenge-only|--trusted-all

  --challenge-only  Build only the trusted Vocabulary and Challenge targets in every workspace.
  --trusted-all     Build Vocabulary, Challenge and Solution explicitly in every workspace.

Use --challenge-only before an adversarial Comparator run.  --trusted-all is
only for a reviewed, trusted checkout.
EOF
}

if [ "$#" -ne 1 ]; then
  usage >&2
  exit 2
fi

case "$1" in
  --challenge-only) build_solution=false ;;
  --trusted-all) build_solution=true ;;
  --help|-h)
    usage
    exit 0
    ;;
  *)
    usage >&2
    exit 2
    ;;
esac

script_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
repo_root=$(CDPATH= cd -- "$script_dir/.." && pwd)

# Deliberately enumerate release workspaces instead of discovering arbitrary
# directories: this driver is part of the reviewed release configuration.
workspaces='
caloric-dirichlet-ball
caloric-smooth
classical-viscosity
schauder-interior
semilinear-comparison
semilinear-existence
semilinear-regularity'

# Fail closed if a new configured workspace has not been added to the reviewed
# allowlist above.  This catches coverage drift without executing arbitrary
# workspace configuration.
for config in "$repo_root"/challenges/*/config.json; do
  workspace=${config%/config.json}
  workspace=${workspace##*/}
  listed=false
  for reviewed_workspace in $workspaces; do
    if [ "$workspace" = "$reviewed_workspace" ]; then
      listed=true
      break
    fi
  done
  if [ "$listed" = false ]; then
    echo "Unreviewed challenge workspace is missing from the driver: $workspace" >&2
    exit 1
  fi
done

for workspace in $workspaces; do
  workspace_dir="$repo_root/challenges/$workspace"
  for required_file in Vocabulary.lean Challenge.lean Solution.lean config.json lakefile.toml; do
    if [ ! -f "$workspace_dir/$required_file" ]; then
      echo "Missing $required_file in challenge workspace: $workspace_dir" >&2
      exit 1
    fi
  done
  if [ -d "$workspace_dir/Challenge" ]; then
    echo "Old Challenge/ vocabulary directory (use Vocabulary/) in: $workspace_dir" >&2
    exit 1
  fi
done

# Every workspace sets `packagesDir = "../../.lake/packages"`, so all of them
# share the root workspace's dependency checkouts and builds (the manifests
# lock identical revisions).  Fetch the Mathlib cache once, at the root.
echo "==> root: dependency cache"
(
  cd "$repo_root"
  lake exe cache get
)

for workspace in $workspaces; do
  workspace_dir="$repo_root/challenges/$workspace"
  echo "==> $workspace: Vocabulary Challenge"
  (
    cd "$workspace_dir"
    lake build Vocabulary Challenge
  )
done

if [ "$build_solution" = true ]; then
  for workspace in $workspaces; do
    workspace_dir="$repo_root/challenges/$workspace"
    echo "==> $workspace: Solution"
    (
      cd "$workspace_dir"
      lake build Solution
    )
  done
fi
