#!/usr/bin/env ruby
# Validate the public theorem inventory against Lean and the challenge configs, and the
# toolchain, dependency, and Comparator tool pins against the files that use them.
require 'yaml'
require 'json'
require 'open3'
require 'tempfile'
require 'pathname'

ROOT = Pathname.new(__dir__).parent
# Lean identifiers may contain Unicode letters and subscripts (e.g. `gradₓ`).
LEAN_NAME = /\A[\p{L}_][\p{L}\p{N}_'!?]*(?:\.[\p{L}_][\p{L}\p{N}_'!?]*)*\z/
metadata_only = ARGV == ['--metadata-only']
abort 'usage: check-formalization-manifest.rb [--metadata-only]' unless ARGV.empty? || metadata_only
Dir.chdir(ROOT)
failures = []
manifest = YAML.safe_load_file('formalization.yaml')
abort 'formalization.yaml must be a mapping' unless manifest.is_a?(Hash)
targets = manifest.fetch('targets')
challenges = manifest.fetch('supplemental_challenges', [])
allowed = manifest.fetch('permitted_axioms')
abort 'targets must be a nonempty list' unless targets.is_a?(Array) && !targets.empty?
abort 'permitted_axioms must be a list' unless allowed.is_a?(Array) && allowed.all? { |a| a.is_a?(String) }
abort 'supplemental_challenges must be a list' unless challenges.is_a?(Array)
abort 'duplicate target/challenge id' unless (targets + challenges).map { |t| t.fetch('id') }.uniq.length == targets.length + challenges.length

lean_names = []
# Targets without a `challenge` key (e.g. packaged assembly theorems whose hypotheses are
# discharged inside other challenges) are checked for name and axioms only.
challenged = (targets + challenges).select { |entry| entry.key?('challenge') }
manifest_configs = challenged.map { |entry| File.join(entry.fetch('challenge'), 'config.json') }.sort
workspace_configs = Dir.glob('challenges/*/config.json').sort
failures << "challenge config inventory differs from manifest: #{(workspace_configs - manifest_configs).inspect} unlisted, #{(manifest_configs - workspace_configs).inspect} missing" unless workspace_configs == manifest_configs
challenged.each do |entry|
  path = entry.fetch('challenge')
  config_path = File.join(path, 'config.json')
  abort "missing #{config_path}" unless File.file?(config_path)
  config = JSON.parse(File.read(config_path))
  expected = entry.fetch('challenge_theorems')
  failures << "#{path}: missing Challenge.lean" unless File.file?(File.join(path, 'Challenge.lean'))
  failures << "#{path}: missing Solution.lean" unless File.file?(File.join(path, 'Solution.lean'))
  failures << "#{path}: missing lakefile.toml" unless File.file?(File.join(path, 'lakefile.toml'))
  failures << "#{path}: challenge_theorems must be a nonempty list" unless expected.is_a?(Array) && !expected.empty?
  failures << "#{path}: theorem_names differ from manifest" unless config.fetch('theorem_names') == expected
  failures << "#{path}: permitted_axioms differ from manifest" unless config.fetch('permitted_axioms').sort == allowed.sort
  failures << "#{path}: unexpected challenge module" unless config.fetch('challenge_module') == 'Challenge'
  failures << "#{path}: unexpected solution module" unless config.fetch('solution_module') == 'Solution'
  expected.each do |name|
    failures << "#{path}: invalid Lean declaration name #{name.inspect}" unless name.match?(LEAN_NAME)
  end
end
targets.each do |target|
  expected_axioms = target.fetch('expected_axioms')
  abort "#{target.fetch('id')}: expected_axioms must be a subset of permitted_axioms" unless (expected_axioms - allowed).empty?
  mod = target.fetch('module')
  path = mod.tr('.', '/') + '.lean'
  failures << "missing module #{path}" unless File.file?(path)
  lean_names << [target.fetch('declaration'), mod]
  target.fetch('related_declarations', []).each { |name| lean_names << [name, mod] }
end
# Toolchain, Mathlib, and dependency pins agree with lean-toolchain and lake-manifest.json, and
# every challenge workspace uses the root toolchain and locks the root's git revisions.
root_toolchain = File.read('lean-toolchain').strip
git_packages = lambda do |file|
  JSON.parse(File.read(file)).fetch('packages').select { |p| p['type'] == 'git' }
      .to_h { |p| [p['name'], [p['rev'], p['inputRev']]] }
end
locked = git_packages.call('lake-manifest.json')
failures << 'lean_toolchain differs from lean-toolchain' unless manifest['lean_toolchain'] == root_toolchain
failures << 'mathlib differs from the locked Mathlib inputRev' unless manifest['mathlib'] == locked.fetch('mathlib')[1]
manifest.fetch('dependencies').each do |dep|
  rev, input_rev = locked.fetch(dep.fetch('name')) { [nil, nil] }
  failures << "dependency #{dep['name']}: rev #{dep['rev'].inspect} differs from the locked inputRev" unless dep['rev'] == input_rev
  failures << "dependency #{dep['name']}: commit differs from the locked rev" unless dep['commit'] == rev
end
workspace_configs.each do |config_path|
  path = File.dirname(config_path)
  toolchain = File.join(path, 'lean-toolchain')
  failures << "#{path}: lean-toolchain differs from the root lean-toolchain" \
    unless File.file?(toolchain) && File.read(toolchain).strip == root_toolchain
  workspace_manifest = File.join(path, 'lake-manifest.json')
  failures << "#{path}: lake-manifest.json locks different git revisions from the root" \
    unless File.file?(workspace_manifest) && git_packages.call(workspace_manifest) == locked
end

# Comparator tool revisions agree with scripts/release-comparator.sh.
tools = manifest.fetch('comparator')
driver = File.read('scripts/release-comparator.sh')
{ 'comparator_revision' => 'COMPARATOR_REV',
  'lean4export_revision' => 'LEAN4EXPORT_REV',
  'landrun_revision' => 'LANDRUN_REV' }.each do |key, var|
  pinned = driver[/^#{var}=(\h+)$/, 1]
  failures << "comparator.#{key} #{tools[key].inspect} differs from #{var} in scripts/release-comparator.sh" \
    unless pinned && tools[key] == pinned
end


abort failures.join("\n") unless failures.empty?
if metadata_only
  puts "Validated #{targets.length} targets (#{challenged.length - challenges.length} challenged) and #{challenges.length} supplemental challenge configs"
  exit 0
end

# One Lean invocation makes name resolution and transitive axiom inspection
# use the same imports and options as the package build.
Tempfile.create(['manifest-check-', '.lean']) do |file|
  file.puts 'import ParabolicBasic'
  lean_names.each_with_index do |(name, _), index|
    abort "invalid Lean declaration name: #{name.inspect}" unless name.match?(LEAN_NAME)
    file.puts %Q(#eval IO.println "MANIFEST_BEGIN_#{index}")
    file.puts "#check #{name}"
    file.puts "#print axioms #{name}" if targets.any? { |t| t['declaration'] == name }
    file.puts %Q(#eval IO.println "MANIFEST_END_#{index}")
  end
  file.flush
  output, status = Open3.capture2e('lake', 'env', 'lean', file.path)
  unless status.success?
    warn output
    abort 'Lean manifest declaration/axiom check failed'
  end
  targets.each do |target|
    name = target.fetch('declaration')
    index = lean_names.index { |pair| pair.first == name }
    output.force_encoding(Encoding::UTF_8)
    section = output[/MANIFEST_BEGIN_#{index}(.*?)MANIFEST_END_#{index}/m, 1]
    abort "missing Lean output for #{name}" unless section
    actual = if section.include?('does not depend on any axioms')
               []
             else
               block = section[/depends on axioms: \[([^\]]*)\]/, 1]
               abort "unrecognized #print axioms output for #{name}: #{section}" unless block
               block.split(',').map(&:strip).uniq
             end
    expected = target.fetch('expected_axioms')
    failures << "#{name}: axioms #{actual.sort.inspect}, expected #{expected.sort.inspect}" unless actual.sort == expected.sort
  end
end
abort failures.join("\n") unless failures.empty?
puts "Validated #{targets.length} targets, #{challenges.length} supplemental challenge configs, and #{lean_names.length} library Lean names"
