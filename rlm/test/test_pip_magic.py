from __future__ import annotations

import os
import stat
import sys
import tempfile
import unittest
from pathlib import Path
from unittest import mock

from rlm import pip as pip_module
from rlm import repl

HASH_A = "a" * 64
HASH_B = "b" * 64
LOCK = (
    "# exported\n"
    f"dill==0.4.1 \\\n    --hash=sha256:{HASH_A} \\\n    --hash=sha256:{HASH_B}\n"
    "    # via eukhe-runtime\n"
    f"colorama==0.4.6 ; sys_platform == 'win32' \\\n    --hash=sha256:{HASH_A}\n"
    f"PyYAML==6.0.3 \\\n    --hash=sha256:{HASH_B}\n"
)


class LockedKernel:
    """A kernel env with a lock and a stand-in uv that records its argv and the requirements it was given."""

    def __init__(self, test: unittest.TestCase, *, uv_exit: int = 0, project: str | None = None) -> None:
        self.dir = Path(tempfile.mkdtemp(prefix="eukhe-pip-test-"))
        test.addCleanup(lambda: __import__("shutil").rmtree(self.dir, ignore_errors=True))
        self.log = self.dir / "uv.log"
        lock = self.dir / "requirements-kernel.txt"
        lock.write_text(LOCK + f"eukhe-absent-dist==1.0 \\\n    --hash=sha256:{HASH_A}\n", encoding="utf-8")
        uv = self.dir / "uv"
        uv.write_text(
            "#!/bin/sh\n"
            f'echo "$@" >> "{self.log}"\n'
            'for arg in "$@"; do case "$arg" in *eukhe-kernel-install-*) cat "$arg" >> "' + str(self.log) + '";; esac; done\n'
            'echo " + dill==0.4.1" >&2\n'
            f"exit {uv_exit}\n",
            encoding="utf-8",
        )
        uv.chmod(uv.stat().st_mode | stat.S_IXUSR)
        env = {pip_module.UV_ENV: str(uv), pip_module.LOCK_ENV: str(lock), "UV_INDEX_URL": "https://evil.invalid"}
        if project is not None:
            project_lock = self.dir / "project.txt"
            project_lock.write_text(project, encoding="utf-8")
            env[pip_module.PROJECT_LOCK_ENV] = str(project_lock)
            env[pip_module.PROJECT_PACKAGES_ENV] = str(self.dir / "project-packages")
        patch = mock.patch.dict(os.environ, env)
        patch.start()
        test.addCleanup(patch.stop)
        os.environ.pop("EUKHE_OFFLINE", None)

    def calls(self) -> str:
        return self.log.read_text(encoding="utf-8") if self.log.exists() else ""


class UnmanagedKernel:
    def __init__(self, test: unittest.TestCase) -> None:
        patch = mock.patch.dict(os.environ)
        patch.start()
        test.addCleanup(patch.stop)
        for name in (pip_module.UV_ENV, pip_module.LOCK_ENV, pip_module.PROJECT_LOCK_ENV):
            os.environ.pop(name, None)


class LockTest(unittest.TestCase):
    def test_a_lock_parses_to_one_line_pins_without_comments(self) -> None:
        self.assertEqual(
            pip_module.parse_lock(LOCK),
            {
                "dill": [f"dill==0.4.1 --hash=sha256:{HASH_A} --hash=sha256:{HASH_B}"],
                "colorama": [f"colorama==0.4.6 ; sys_platform == 'win32' --hash=sha256:{HASH_A}"],
                "pyyaml": [f"PyYAML==6.0.3 --hash=sha256:{HASH_B}"],
            },
        )
        self.assertEqual(pip_module.pinned_version(pip_module.parse_lock(LOCK)["colorama"][0]), "0.4.6")

    def test_a_specifier_is_checked_against_the_locked_version(self) -> None:
        for spec, locked, allowed in (
            ("", "2.5.4", True),
            ("==2.5.4", "2.5.4", True),
            ("==2.5.3", "2.5.4", False),
            ("==2.*", "2.5.4", True),
            (">=2,<3", "2.5.4", True),
            (">=2.6", "2.5.4", False),
            ("<2", "2.5.4", False),
            ("!=2.5.4", "2.5.4", False),
            ("~=2.5.0", "2.5.4", True),
            ("~=2.4.0", "2.5.4", False),
            (">=1.0rc1", "2.5.4", False),
            ("@ https://x", "2.5.4", False),
        ):
            with self.subTest(spec=spec):
                self.assertEqual(pip_module.specifier_allows(spec, locked), allowed)


class InstallTest(unittest.TestCase):
    def test_a_locked_package_installs_with_its_hashes_and_the_locks_as_constraints(self) -> None:
        kernel = LockedKernel(self, project=f"rich==14.0.0 \\\n    --hash=sha256:{HASH_A}\n")
        self.assertEqual(pip_module.install(["Dill", "rich"]), ["+ dill==0.4.1", "+ dill==0.4.1"])
        shared, shared_pins, project, project_pins = kernel.calls().splitlines()[:4]
        lock = os.environ[pip_module.LOCK_ENV]
        project_lock = os.environ[pip_module.PROJECT_LOCK_ENV]
        packages = os.environ[pip_module.PROJECT_PACKAGES_ENV]
        start = f"pip install --no-config --python {sys.executable} --require-hashes --only-binary :all: -r "
        # Eukhe's package goes into the kernel env, with Eukhe's lock alone.
        self.assertTrue(shared.startswith(start) and shared.endswith(f" -c {lock}"), shared)
        self.assertEqual(shared_pins, f"dill==0.4.1 --hash=sha256:{HASH_A} --hash=sha256:{HASH_B}")
        # The project's goes beside it, with both locks.
        self.assertTrue(
            project.startswith(start) and project.endswith(f" -c {lock} -c {project_lock} --target {packages}"),
            project,
        )
        self.assertEqual(project_pins, f"rich==14.0.0 --hash=sha256:{HASH_A}")
        self.assertNotIn("--offline", kernel.calls())

    def test_offline_installs_from_the_cache_only(self) -> None:
        kernel = LockedKernel(self)
        with mock.patch.dict(os.environ, {"EUKHE_OFFLINE": "1"}):
            pip_module.install(["dill"])
        self.assertIn(" --offline\n", kernel.calls())

    def test_a_package_outside_the_locks_is_refused_with_the_lock_command(self) -> None:
        kernel = LockedKernel(self)
        with self.assertRaises(pip_module.PackageError) as refused:
            pip_module.install(["rich"])
        self.assertEqual(
            str(refused.exception),
            "rich is not in Eukhe's package lock or this project's. The kernel installs only locked packages "
            "(exact versions with hashes), so every machine runs the same ones. Lock it for this project with "
            "`eukhe kernel lock rich` (a shell command: it resolves the package once, records its exact versions "
            "and hashes in .eukhe/requirements-kernel.txt, and needs internet); then import it.",
        )
        self.assertEqual(kernel.calls(), "", "uv never ran")

    def test_a_failed_install_reports_uv(self) -> None:
        LockedKernel(self, uv_exit=2)
        with self.assertRaises(pip_module.PackageError) as failed:
            pip_module.install(["dill"])
        self.assertIn("installing dill from the lock failed", str(failed.exception))

    def test_an_unmanaged_interpreter_installs_nothing(self) -> None:
        UnmanagedKernel(self)
        with self.assertRaises(pip_module.PackageError) as refused:
            pip_module.magic("install dill")
        self.assertIn("EUKHE_KERNEL_PYTHON", str(refused.exception))


class MagicTest(unittest.TestCase):
    def test_pip_lines_become_calls_and_python_stays_as_it_is(self) -> None:
        self.assertIsNone(pip_module.expand_magics("x = 1\nprint(x % 2)"))
        cell = "%pip install requests 'httpx>=0.27'\nif True:\n    %pip\nimport requests"
        self.assertEqual(
            pip_module.expand_magics(cell),
            "__import__('rlm.pip', fromlist=['magic']).magic(\"install requests 'httpx>=0.27'\")\n"
            "if True:\n"
            "    __import__('rlm.pip', fromlist=['magic']).magic('')\n"
            "import requests",
        )

    def test_a_cell_with_pip_lines_compiles_line_for_line(self) -> None:
        codes, trailing = repl._compile_cell("x = 1\n%pip install dill\ny = 2", "<cell-pip>")
        self.assertFalse(trailing)
        self.assertEqual(len(codes), 1)
        with self.assertRaises(SyntaxError):
            repl._compile_cell("x = (\n%pip install a", "<cell-broken>")

    def test_pip_install_takes_the_locked_version_and_ignores_pip_only_options(self) -> None:
        kernel = LockedKernel(self)
        pip_module.magic("install -q --upgrade 'dill>=0.4' pyyaml")
        calls = kernel.calls()
        self.assertIn("dill==0.4.1 --hash", calls)
        self.assertIn("PyYAML==6.0.3 --hash", calls)

    def test_pip_install_refuses_another_version_a_path_and_other_commands(self) -> None:
        kernel = LockedKernel(self)
        for args, message in (
            ("install dill==0.3.8", "the lock pins dill 0.4.1, which `dill==0.3.8` does not accept"),
            ("install ./wheel.whl", "`%pip install ./wheel.whl` is not supported"),
            ("install -r requirements.txt", "`%pip install -r` is not supported"),
            ("install rich", "rich is not in Eukhe's package lock or this project's"),
            ("install", "`%pip install` needs a package name"),
            ("uninstall dill", "`%pip` runs `install <name>...`"),
            ("", "`%pip` runs `install <name>...`"),
        ):
            with self.subTest(args=args):
                with self.assertRaises(pip_module.PackageError) as refused:
                    pip_module.magic(args)
                self.assertIn(message, str(refused.exception))
        self.assertEqual(kernel.calls(), "", "uv never ran")


class ImportTest(unittest.TestCase):
    def test_a_missing_module_outside_the_locks_names_the_lock_command(self) -> None:
        LockedKernel(self)
        try:
            import eukhe_absent_module_xyz  # noqa: F401
        except ModuleNotFoundError as error:
            event = repl._error_event("c1", error)
        self.assertEqual(event["ename"], "ModuleNotFoundError")
        self.assertIn("`eukhe kernel lock eukhe_absent_module_xyz`", event["traceback"][-1])
        other = repl._error_event("c2", ValueError("no"))
        self.assertNotIn("kernel lock", "".join(other["traceback"]))

    def test_own_code_importing_a_locked_module_installs_it_once(self) -> None:
        kernel = LockedKernel(self)
        finder = pip_module.LockedPackageFinder()
        namespace: dict[str, object] = {"finder": finder}
        # A cell's frame: its file name is not a file of the interpreter.
        exec(compile("spec = finder.find_spec('eukhe_absent_dist')", "<cell-1>", "exec"), namespace)
        self.assertIsNone(namespace["spec"], "the stand-in uv installs nothing, so the module is still missing")
        self.assertIn("eukhe-absent-dist==1.0 --hash", kernel.calls())
        before = kernel.calls()
        exec(compile("spec = finder.find_spec('eukhe_absent_dist')", "<cell-2>", "exec"), namespace)
        self.assertEqual(kernel.calls(), before, "one attempt per module")

    def test_a_library_probing_for_a_locked_module_installs_nothing(self) -> None:
        kernel = LockedKernel(self)
        finder = pip_module.LockedPackageFinder()
        library = os.path.join(sys.base_prefix, "lib", "probe.py")
        exec(compile("spec = finder.find_spec('dill')", library, "exec"), {"finder": finder})
        self.assertIsNone(finder.find_spec("dill.sub", ["x"]))
        self.assertIsNone(finder.find_spec("eukhe_absent_module_xyz"))
        self.assertEqual(kernel.calls(), "")
        self.assertIn("dill is in the package lock", pip_module.missing_module_hint("dill"))


if __name__ == "__main__":
    unittest.main()
