"""Packages for the kernel: installed on demand, only from a lock.

The kernel starts on the standard library alone. A package is installed the
first time code needs it, at the one version a lock names and only after
its files match the lock's hashes (``uv pip install --require-hashes``), so
every machine gets the same files:

- Eukhe's lock (``eukhe-runtime/requirements-kernel.txt``) ships with
  Eukhe. ``import numpy`` in a cell, a skill or the runtime itself installs
  the locked numpy and its locked dependencies, then imports it.
- A project lock (``<project>/.eukhe/requirements-kernel.txt``, written by
  ``eukhe kernel lock <package>``) extends it for one project.
- A package in neither lock is refused, with the command that locks it.

``%pip install <name>`` follows the same rule: it installs the locked
version, or refuses. The host passes the pinned uv and the locks in
``EUKHE_KERNEL_UV``, ``EUKHE_KERNEL_LOCK``, ``EUKHE_KERNEL_PROJECT_LOCK`` and
``EUKHE_KERNEL_PROJECT_PACKAGES`` (the directory the project lock's packages
go to, at the end of ``sys.path``: the env that every project shares holds
only packages of Eukhe's lock). A kernel on an interpreter Eukhe does not manage (``EUKHE_KERNEL_PYTHON``)
has none of them and installs nothing.
"""

from __future__ import annotations

import importlib
import importlib.abc
import importlib.util
import os
import re
import shlex
import subprocess
import sys
import tempfile
from pathlib import Path

UV_ENV = "EUKHE_KERNEL_UV"
LOCK_ENV = "EUKHE_KERNEL_LOCK"
PROJECT_LOCK_ENV = "EUKHE_KERNEL_PROJECT_LOCK"
PROJECT_PACKAGES_ENV = "EUKHE_KERNEL_PROJECT_PACKAGES"
# The command that adds a package to the project lock.
LOCK_COMMAND = "eukhe kernel lock"

# A ``%pip`` line, at any indentation: the rest of the line is pip's argv.
_MAGIC_LINE = re.compile(r"^(?P<indent>[ \t]*)%pip(?:[ \t]+(?P<args>.*?))?[ \t]*$")
# ``name[extras]<specifier>`` of a ``%pip install`` argument.
_REQUIREMENT = re.compile(r"^(?P<name>[A-Za-z0-9][A-Za-z0-9._-]*)(?:\[[^\]]*\])?(?P<spec>.*)$")
_CLAUSE = re.compile(r"^(?P<op>===|==|!=|~=|<=|>=|<|>)\s*(?P<version>[^\s,;]+)$")
# `pip install` options that change nothing here: the lock decides the
# version and the kernel env is the only target.
_IGNORED_INSTALL_OPTIONS = frozenset(
    {"-q", "-qq", "--quiet", "-U", "--upgrade", "--user", "--no-cache-dir", "--break-system-packages"}
)
# Import names that differ from their distribution's name (after
# normalization) among the packages of Eukhe's lock.
_DISTRIBUTION_OF_IMPORT = {
    "attr": "attrs",
    "bs4": "beautifulsoup4",
    "dateutil": "python-dateutil",
    "dotenv": "python-dotenv",
    "PIL": "pillow",
    "yaml": "pyyaml",
}
# uv settings a user's environment may carry into the install; every other
# `UV_*` variable is dropped so it cannot change what is installed.
_UV_ENV_KEPT = frozenset({"UV_CACHE_DIR", "UV_NATIVE_TLS", "UV_HTTP_TIMEOUT"})


class PackageError(RuntimeError):
    """A package could not be installed from a lock."""


def normalize(name: str) -> str:
    """The canonical distribution name (PEP 503)."""
    return re.sub(r"[-_.]+", "-", name).lower()


def parse_lock(text: str) -> dict[str, list[str]]:
    """Each distribution's pinned requirements of a hashed requirements file.

    A requirement is ``name==version [; marker] --hash=...`` over continuation
    lines; comments are dropped. A name has several requirements when the
    lock pins it per platform.
    """
    pins: dict[str, list[str]] = {}
    current: list[str] = []

    def close() -> None:
        if not current:
            return
        joined = " ".join(part.rstrip("\\").strip() for part in current)
        name = joined.split("==", 1)[0].strip()
        pins.setdefault(normalize(name), []).append(joined)
        current.clear()

    for line in text.splitlines():
        stripped = line.strip()
        if not stripped or stripped.startswith("#"):
            continue
        if line[0] in " \t":
            if current:
                current.append(stripped)
            continue
        close()
        current.append(stripped)
    close()
    return pins


def pinned_version(requirement: str) -> str:
    """The version of one pinned requirement of a lock."""
    return requirement.split("==", 1)[1].split()[0].rstrip(";")


class Locks:
    """The locks of this kernel: Eukhe's, then the project's."""

    def __init__(self, uv: str, lock: str, project_lock: str | None, project_packages: str | None) -> None:
        self.uv = uv
        self.files = [lock] + ([project_lock] if project_lock and project_packages else [])
        # Where the project lock's packages go: beside the kernel env, at
        # the end of sys.path, so a project's packages never change the
        # env other projects share and Eukhe's locked versions win.
        self.project_packages = project_packages
        self._stamp: tuple[tuple[str, float], ...] | None = None
        self._pins: dict[str, list[str]] = {}
        self._own: frozenset[str] = frozenset()

    def pins(self) -> dict[str, list[str]]:
        """Every pin, read again when a lock file changed (a project lock grows mid-session)."""
        stamp = tuple((path, os.stat(path).st_mtime) for path in self.files if os.path.isfile(path))
        if stamp != self._stamp:
            merged: dict[str, list[str]] = {}
            for path, _ in stamp:
                parsed = parse_lock(Path(path).read_text(encoding="utf-8"))
                if path == self.files[0]:
                    self._own = frozenset(parsed)
                for name, requirements in parsed.items():
                    merged.setdefault(name, requirements)
            self._pins = merged
            self._stamp = stamp
        return self._pins

    def in_eukhes_lock(self, name: str) -> bool:
        self.pins()
        return normalize(name) in self._own


def locks() -> Locks | None:
    """The kernel's locks, or None on an interpreter Eukhe does not manage."""
    uv = os.environ.get(UV_ENV)
    lock = os.environ.get(LOCK_ENV)
    if not uv or not lock:
        return None
    global _LOCKS
    if _LOCKS is None or _LOCKS.uv != uv or _LOCKS.files[0] != lock:
        _LOCKS = Locks(
            uv, lock, os.environ.get(PROJECT_LOCK_ENV) or None, os.environ.get(PROJECT_PACKAGES_ENV) or None
        )
    return _LOCKS


_LOCKS: Locks | None = None


def _release(version: str) -> tuple[int, ...] | None:
    parts = version.split(".")
    if not all(part.isdigit() for part in parts):
        return None
    return tuple(int(part) for part in parts)


def _clause_allows(op: str, wanted: str, locked: str) -> bool:
    if op in ("==", "===") and "*" not in wanted:
        return wanted == locked
    if op == "==":
        return locked.startswith(wanted.rstrip("*"))
    have, want = _release(locked), _release(wanted)
    if have is None or want is None:
        return False
    width = max(len(have), len(want))
    padded_have = have + (0,) * (width - len(have))
    padded_want = want + (0,) * (width - len(want))
    if op == "!=":
        return padded_have != padded_want
    if op == ">=":
        return padded_have >= padded_want
    if op == "<=":
        return padded_have <= padded_want
    if op == ">":
        return padded_have > padded_want
    if op == "<":
        return padded_have < padded_want
    # `~=X.Y.Z`: at least it, within X.Y.
    return padded_have >= padded_want and have[: len(want) - 1] == want[:-1]


def specifier_allows(spec: str, locked: str) -> bool:
    """Does the version specifier of a request accept the locked version."""
    for clause in filter(None, (part.strip() for part in spec.split(","))):
        match = _CLAUSE.match(clause)
        if match is None or not _clause_allows(match.group("op"), match.group("version"), locked):
            return False
    return True


def not_locked(name: str) -> str:
    """The refusal of a package no lock names."""
    return (
        f"{name} is not in Eukhe's package lock or this project's. The kernel installs only locked packages "
        f"(exact versions with hashes), so every machine runs the same ones. Lock it for this project with "
        f"`{LOCK_COMMAND} {name}` (a shell command: it resolves the package once, records its exact versions and "
        f"hashes in .eukhe/requirements-kernel.txt, and needs internet); then import it."
    )


def _uv_env() -> dict[str, str]:
    return {key: value for key, value in os.environ.items() if not key.startswith("UV_") or key in _UV_ENV_KEPT}


def _offline() -> bool:
    return os.environ.get("EUKHE_OFFLINE", "").lower() in ("1", "true", "yes")


def _uv(found: Locks, args: list[str]) -> subprocess.CompletedProcess[str]:
    argv = [found.uv, "pip", args[0], "--no-config", "--python", sys.executable, *args[1:]]
    return subprocess.run(argv, stdin=subprocess.DEVNULL, capture_output=True, text=True, env=_uv_env(), check=False)


def install(names: list[str]) -> list[str]:
    """Install the locked versions of `names` and of what they need; the lines uv reports as installed.

    Raises PackageError for a name no lock holds, or when uv fails (a hash
    that does not match, no network and nothing cached).
    """
    found = locks()
    if found is None:
        raise PackageError(
            "this kernel runs on an interpreter Eukhe does not manage (EUKHE_KERNEL_PYTHON), "
            "so Eukhe installs no package into it; install it into that interpreter yourself"
        )
    pins = found.pins()
    shared: list[str] = []
    project: list[str] = []
    for name in names:
        requirements = pins.get(normalize(name))
        if requirements is None:
            raise PackageError(not_locked(name))
        (shared if found.in_eukhes_lock(name) else project).extend(requirements)
    installed: list[str] = []
    for wanted, target in ((shared, None), (project, found.project_packages)):
        if wanted:
            installed += _install_pins(found, names, wanted, target)
    importlib.invalidate_caches()
    return installed


def _install_pins(found: Locks, names: list[str], wanted: list[str], target: str | None) -> list[str]:
    with tempfile.NamedTemporaryFile("w", suffix=".txt", prefix="eukhe-kernel-install-", delete=False) as direct:
        direct.write("\n".join(wanted) + "\n")
    try:
        args = ["install", "--require-hashes", "--only-binary", ":all:", "-r", direct.name, "-c", found.files[0]]
        if target is not None:
            args += ["-c", found.files[1], "--target", target]
        if _offline():
            args.append("--offline")
        done = _uv(found, args)
    finally:
        os.unlink(direct.name)
    if done.returncode != 0:
        detail = "\n".join(done.stderr.strip().splitlines()[-12:])
        raise PackageError(
            f"installing {', '.join(names)} from the lock failed (the locked files are downloaded once, "
            f"which needs internet):\n{detail}"
        )
    if target is not None:
        _use_project_packages(target)
    return [line.strip() for line in done.stderr.splitlines() if line.lstrip().startswith("+ ")]


def _use_project_packages(target: str) -> None:
    if os.path.isdir(target) and target not in sys.path:
        sys.path.append(target)


def distribution_of(module: str) -> str | None:
    """The locked distribution that provides the top-level module `module`, if any."""
    found = locks()
    if found is None:
        return None
    name = normalize(_DISTRIBUTION_OF_IMPORT.get(module, module))
    return name if name in found.pins() else None


# The file of `importlib.import_module` when importlib is not frozen.
_IMPORT_MODULE_FILE = os.path.join("importlib", "__init__.py")


def _imported_by_own_code() -> bool:
    """Is the import in flight written in a cell, a skill, the runtime or the project.

    An import inside the standard library or an installed package (a library
    probing for an optional dependency) installs nothing, nor does an
    ``importlib.util.find_spec`` probe.
    """
    frame = sys._getframe(1)
    here = __file__
    while frame is not None:
        filename = frame.f_code.co_filename
        # Skip this finder, the import machinery and `importlib.import_module`.
        machinery = (
            filename.startswith("<frozen importlib._bootstrap")
            or filename == "<frozen importlib>"
            or filename.endswith(_IMPORT_MODULE_FILE)
        )
        if filename != here and not machinery:
            break
        frame = frame.f_back
    if frame is None:
        return False
    filename = frame.f_code.co_filename
    if filename.startswith("<frozen"):
        return False
    if filename.startswith("<"):
        return True
    real = os.path.realpath(filename)
    return not any(
        real.startswith(os.path.realpath(prefix) + os.sep) for prefix in {sys.prefix, sys.base_prefix}
    )


class LockedPackageFinder(importlib.abc.MetaPathFinder):
    """The last finder of ``sys.meta_path``: a top-level module nothing else found.

    When Eukhe's lock or the project's names its distribution, and the import
    is written in own code, the locked distribution is installed and the
    import goes on. Each module is tried once per kernel; a failed install
    is kept in `failures` for the error the cell shows.
    """

    def __init__(self) -> None:
        self.tried: set[str] = set()
        self.failures: dict[str, str] = {}

    def find_spec(self, fullname, path=None, target=None):  # noqa: ANN001, ANN201 - the finder protocol
        if path is not None or "." in fullname or fullname in self.tried:
            return None
        distribution = distribution_of(fullname)
        if distribution is None or not _imported_by_own_code():
            return None
        self.tried.add(fullname)
        try:
            installed = install([distribution])
        except PackageError as error:
            self.failures[fullname] = str(error)
            return None
        print(
            f"[eukhe] installed {distribution} from the package lock ({', '.join(installed) or 'already present'})",
            file=sys.stderr,
        )
        return importlib.util.find_spec(fullname)


_FINDER = LockedPackageFinder()


def install_import_hook() -> None:
    """Put the locked-package finder at the end of ``sys.meta_path`` (once), and the project's packages on ``sys.path``."""
    if _FINDER not in sys.meta_path:
        sys.meta_path.append(_FINDER)
    found = locks()
    if found is not None and found.project_packages:
        _use_project_packages(found.project_packages)


def missing_module_hint(module: str) -> str:
    """What a cell's ModuleNotFoundError for `module` adds to its traceback."""
    top = module.split(".", 1)[0]
    failure = _FINDER.failures.get(top)
    if failure is not None:
        return failure + "\n"
    if locks() is None:
        return (
            f"This kernel runs on an interpreter Eukhe does not manage (EUKHE_KERNEL_PYTHON); "
            f"install the distribution that provides {top!r} into it yourself.\n"
        )
    distribution = distribution_of(top)
    if distribution is not None:
        return (
            f"{distribution} is in the package lock: a `%pip install {distribution}` line in a cell installs it "
            f"(an `import {top}` written in a cell does too).\n"
        )
    return not_locked(top) + " Distribution names can differ from import names.\n"


def expand_magics(code: str) -> str | None:
    """The cell with every ``%pip`` line turned into a call, or None when it has none."""
    lines = code.split("\n")
    changed = False
    for index, line in enumerate(lines):
        match = _MAGIC_LINE.match(line)
        if match is None:
            continue
        args = match.group("args") or ""
        lines[index] = f"{match.group('indent')}__import__('rlm.pip', fromlist=['magic']).magic({args!r})"
        changed = True
    return "\n".join(lines) if changed else None


def _install_magic(found: Locks, argv: list[str]) -> None:
    names: list[str] = []
    pins = found.pins()
    for arg in argv:
        if arg in _IGNORED_INSTALL_OPTIONS:
            continue
        match = _REQUIREMENT.match(arg)
        if arg.startswith("-") or match is None or "/" in arg or "@" in arg:
            raise PackageError(
                f"`%pip install {arg}` is not supported: the kernel installs only locked packages, by name "
                f"(`%pip install <name>`). To lock a package for this project run `{LOCK_COMMAND} <requirement>`."
            )
        name, spec = match.group("name"), match.group("spec").strip()
        requirements = pins.get(normalize(name))
        if requirements is None:
            raise PackageError(not_locked(name))
        locked = pinned_version(requirements[0])
        if spec and not specifier_allows(spec, locked):
            raise PackageError(
                f"the lock pins {name} {locked}, which `{arg}` does not accept. The kernel installs the locked "
                f"version only; another version of a package Eukhe's lock pins cannot be installed."
            )
        names.append(name)
    if not names:
        raise PackageError("`%pip install` needs a package name")
    installed = install(names)
    for name in names:
        locked = pinned_version(pins[normalize(name)][0])
        print(f"{name} {locked} (locked)" + ("" if installed else ": already installed"))
    for line in installed:
        print(line)


def magic(args: str) -> None:
    """``%pip <args>``: ``install <name>...`` from the locks; ``list``, ``show``, ``freeze``, ``check`` as uv's."""
    argv = shlex.split(args)
    found = locks()
    if found is None:
        raise PackageError(
            "%pip is not available: this kernel runs on an interpreter Eukhe does not manage (EUKHE_KERNEL_PYTHON)"
        )
    command = argv[0] if argv else ""
    if command == "install":
        _install_magic(found, argv[1:])
    elif command in ("list", "show", "freeze", "check"):
        done = _uv(found, argv)
        sys.stdout.write(done.stdout)
        sys.stderr.write(done.stderr)
        if done.returncode != 0:
            raise PackageError(f"`%pip {args}` failed (uv exited with status {done.returncode})")
    else:
        raise PackageError(
            "`%pip` runs `install <name>...` (the locked version of each package), `list`, `show <name>`, "
            f"`freeze` and `check`. A package outside the locks is added with `{LOCK_COMMAND} <requirement>`."
        )
