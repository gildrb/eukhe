# The shell lines that precompile a payload's Python: the kernel runtime
# (rlm/; eukhe-runtime/ in older release archives) and the bundled skills,
# which every kernel imports at boot. The store is read-only, so a kernel
# could not write their bytecode cache and would compile them again at
# every boot. Hash-based and unchecked: a store file never changes, and its
# mtime says nothing. The kernel runs the CPython eukhe fetches
# (kernel-toolchain.json pins it); bytecode is per minor version, so
# nixpkgs' CPython of that minor writes it, and the build fails when the
# runtime's pyproject.toml asks for another minor.
{ lib, python314 }:
payload: ''
  required=$(sed -n 's/^requires-python = "==\(.*\)\.\*"$/\1/p' "${payload}"/*/pyproject.toml)
  if [ "$required" != "${lib.versions.majorMinor python314.version}" ]; then
    echo "the kernel runtime requires Python $required, not ${lib.versions.majorMinor python314.version}: update nix/kernel-bytecode.nix" >&2
    exit 1
  fi
  ${python314.interpreter} -m compileall -q --invalidation-mode unchecked-hash "${payload}"
''
