#!/usr/bin/env python3
"""Test battery for the bundled-catalog build asset (catalog spec §5 gates).

Offline: `generate` must produce an asset that passes the FULL validation
gates, the packer must hard-fail on missing/invalid assets (negative tests),
and the asset must land in the release tarball layout (assemble + verify
against a synthetic repo tree, the eukhe-release.yml pipeline shape).

Run: python3 .github/scripts/release/test_catalog_assets.py  (or: make catalog-assets-gates)
"""

from __future__ import annotations

import contextlib
import hashlib
import io
import json
import os
import shutil
import subprocess
import sys
import tarfile
import tempfile
import time
import unittest
from pathlib import Path

SCRIPTS_DIR = Path(__file__).resolve().parent
REPO = SCRIPTS_DIR.parents[2]
sys.path.insert(0, str(SCRIPTS_DIR))

import bundle_catalog  # noqa: E402  (same release-scripts directory)
from assemble_artifacts import TARGET_ALIASES  # noqa: E402  (same directory)

BUNDLER = SCRIPTS_DIR / "bundle_catalog.py"
ASSEMBLER = SCRIPTS_DIR / "assemble_artifacts.py"
VERIFIER = SCRIPTS_DIR / "verify_release.py"
PACKER = REPO / ".github" / "scripts" / "package_release.py"

HOST_TARGET = "x86_64-unknown-linux-gnu"
# Archives carry the platform alias (eukhe-<version>-<platform>.tar.gz, the
# asset name eukhe-release.yml publishes and nix/release.json records).
HOST_ARCHIVE_PLATFORM = TARGET_ALIASES[HOST_TARGET]


def run_cli(script, args, env_extra=None, cwd=None):
    env = dict(os.environ)
    if env_extra:
        env.update(env_extra)
    return subprocess.run(
        [sys.executable, str(script), *args],
        capture_output=True, text=True, env=env, cwd=cwd or REPO, check=False,
    )


# A one-pin hash-locked runtime requirements file (the assembler's gate).
FIXTURE_RUNTIME_LOCK = "dill==0.4.1 \\\n    --hash=sha256:" + "a" * 64 + "\n"


class SyntheticRepo:
    """A minimal repo tree the assembler/verifier/packer accept."""

    def __init__(self, root: Path, version: str = "9.9.9"):
        self.root = root
        self.version = version
        (root / "skills").mkdir(parents=True)
        (root / "skills" / "skill.md").write_text("# skill\n")
        (root / "LICENSE").write_text("license\n")
        (root / "README.md").write_text("readme\n")
        runtime = root / "runtime"
        runtime.mkdir()
        (runtime / "pyproject.toml").write_text("[project]\nname='rlm'\n")
        (runtime / "requirements-kernel.txt").write_text(FIXTURE_RUNTIME_LOCK)
        (runtime / "src").mkdir()
        # The exe-adjacent kernel runtime tree package_release.py stages.
        kernel = root / "rlm"
        (kernel / "src" / "rlm").mkdir(parents=True)
        (kernel / "pyproject.toml").write_text("[project]\nname='rlm'\n")
        (kernel / "requirements-kernel.txt").write_text(FIXTURE_RUNTIME_LOCK)
        (kernel / "src" / "rlm" / "repl.py").write_text("# repl\n")
        (runtime / "src" / "repl.py").write_text("# repl\n")
        source = root / "eukhe.c"
        source.write_text(f'#include <stdio.h>\nint main(void) {{ puts("{version}"); return 0; }}\n')
        self.raw_binary = root / "bin" / "cargo-eukhe"
        self.raw_binary.parent.mkdir()
        subprocess.run(["gcc", "-g", "-Wl,--build-id", "-o",
                        str(self.raw_binary), str(source)], check=True)
        self.binary = root / "bin" / "eukhe"
        self.decoder = root / "bin" / f"eukhe-{version}-{HOST_ARCHIVE_PLATFORM}.debug.gz"
        split = run_cli(SCRIPTS_DIR / "split_debug.py", [
            "--binary", str(self.raw_binary), "--shipped", str(self.binary),
            "--out", str(self.binary.parent), "--version", version, "--target", HOST_TARGET])
        if split.returncode:
            raise AssertionError(split.stderr)

    def assemble(self, out_dir, catalog_assets=None, target=HOST_TARGET):
        args = [
            "--repo-root", str(self.root), "--version", self.version,
            "--target", target, "--binary", str(self.binary),
            "--decoder", str(self.decoder),
            "--runtime-dir", str(self.root / "runtime"),
            "--out-dir", str(out_dir),
        ]
        if catalog_assets is not None:
            args += ["--catalog-assets", str(catalog_assets)]
        return run_cli(ASSEMBLER, args)


class ValidationGates(unittest.TestCase):

    def test_generate_passes_the_full_gates(self):
        """Offline build verifier: `generate` produces a VALIDATED asset
        (>= 20 transport tuples) without any network."""
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "assets"
            result = run_cli(BUNDLER, ["generate", "--out", str(out)])
            self.assertEqual(result.returncode, 0, result.stderr)
            facts = json.loads(result.stdout)
            self.assertGreaterEqual(facts["models"]["transportTuples"],
                                    bundle_catalog.MIN_MODEL_TRANSPORT_TUPLES)
            # The verify command (no small-fixture waiver) agrees.
            verify = run_cli(BUNDLER, ["verify", "--out", str(out)])
            self.assertEqual(verify.returncode, 0, verify.stderr)
            self.assertEqual(json.loads(verify.stdout)["models"], facts["models"])

    def test_models_body_matches_the_catalog_contract(self):
        models = json.loads(bundle_catalog.models_body())
        self.assertEqual(set(models), {"schemaVersion", "models"})
        self.assertEqual(models["schemaVersion"], 1)
        seen_tuples = set()
        for model in models["models"]:
            # Strict model schema (spec §1.1): no headers, bounded fields.
            self.assertNotIn("headers", model)
            for field in ("id", "name"):
                self.assertTrue(1 <= len(model[field]) <= 1024)
                self.assertFalse(any(ord(ch) < 0x20 for ch in model[field]))
            self.assertLessEqual(len(model["provider"]), 128)
            self.assertLessEqual(len(model["baseUrl"]), 2048)
            self.assertLessEqual(len(model["input"]), 2)
            self.assertTrue(set(model["input"]) <= {"text", "image"})
            self.assertIn(model["api"], ("anthropic-messages", "openai-completions",
                                        "openai-responses", "bedrock-converse-stream",
                                        "google-generative-ai", "google-vertex",
                                        "mistral-conversations", "openai-codex-responses",
                                        "azure-openai-responses"))
            for cost in model["cost"].values():
                self.assertTrue(0 <= cost <= 1_000_000)
            self.assertLessEqual(model["contextWindow"], 100_000_000)
            self.assertLessEqual(model["maxTokens"], 100_000_000)
            seen_tuples.add((model["provider"], model["api"], model["baseUrl"]))
        self.assertGreaterEqual(len(seen_tuples), bundle_catalog.MIN_MODEL_TRANSPORT_TUPLES)

    def test_validation_rejects_bad_envelopes_and_minimums(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp)
            (out / "models.bundled.json").write_text(
                json.dumps({"schemaVersion": 1, "models": []}))
            with self.assertRaises(SystemExit):
                bundle_catalog.validate_bundled_model_catalog(
                    out / "models.bundled.json")  # 0 tuples < 20
            small = {"schemaVersion": 1, "models": [json.loads(
                bundle_catalog.models_body())["models"][0]]}
            (out / "models.bundled.json").write_text(json.dumps(small))
            # The small-fixture waiver skips the minimum-count gate only.
            bundle_catalog.validate_bundled_model_catalog(
                out / "models.bundled.json", allow_small_fixture=True)
            (out / "models.bundled.json").write_text(
                json.dumps(dict(small, schemaVersion=2)))
            with self.assertRaises(SystemExit):
                bundle_catalog.validate_bundled_model_catalog(
                    out / "models.bundled.json", allow_small_fixture=True)
            # A missing asset fails the dir gate with an actionable message.
            with contextlib.redirect_stderr(io.StringIO()) as captured, \
                    self.assertRaises(SystemExit):
                bundle_catalog.validate_bundled_catalog_dir(out / "nowhere")
            self.assertIn("Missing bundled catalog asset", captured.getvalue())

    def test_small_fixture_verify_waiver(self):
        with tempfile.TemporaryDirectory() as tmp:
            out = Path(tmp) / "assets"
            out.mkdir()
            small_models = {"schemaVersion": 1, "models": [
                {"id": "x", "name": "X", "api": "openai-responses",
                 "provider": "openai", "baseUrl": "https://api.openai.com/v1",
                 "reasoning": False, "input": ["text"],
                 "cost": {"input": 0, "output": 0, "cacheRead": 0, "cacheWrite": 0},
                 "contextWindow": 128000, "maxTokens": 4096}]}
            (out / "models.bundled.json").write_text(json.dumps(small_models))
            strict = run_cli(BUNDLER, ["verify", "--out", str(out)])
            self.assertNotEqual(strict.returncode, 0)
            self.assertIn("transport tuples", strict.stderr)
            waived = run_cli(BUNDLER,
                             ["verify", "--out", str(out), "--allow-small-fixture"])
            self.assertEqual(waived.returncode, 0, waived.stderr)

    def test_validator_rejects_models_missing_required_fields(self):
        """The packaging gate must reject model entries the runtime's strict
        parse would drop (missing cost/contextWindow pass the tuple count but
        fail the runtime schema)."""
        with tempfile.TemporaryDirectory() as tmp:
            models = {"schemaVersion": 1, "models": [json.loads(
                bundle_catalog.models_body())["models"][0]]}
            del models["models"][0]["cost"]
            del models["models"][0]["contextWindow"]
            path = Path(tmp) / "models.bundled.json"
            path.write_text(json.dumps(models))
            with self.assertRaises(SystemExit):
                bundle_catalog.validate_bundled_model_catalog(
                    path, allow_small_fixture=True)


class PackerGates(unittest.TestCase):
    """The release packer must hard-fail without validated assets, and valid
    assets must land in the release tarball layout."""

    def setUp(self):
        self._tmp = tempfile.TemporaryDirectory()
        self.tmp = Path(self._tmp.name)
        self.assets = self.tmp / "catalog-assets"
        result = run_cli(BUNDLER, ["generate", "--out", str(self.assets)])
        self.assertEqual(result.returncode, 0, result.stderr)
        self.repo = SyntheticRepo(self.tmp / "synrepo")

    def tearDown(self):
        shutil.rmtree(self.tmp, ignore_errors=True)
        self._tmp.cleanup()

    def test_packer_fails_without_catalog_assets(self):
        out = self.tmp / "dist-missing"
        result = self.repo.assemble(out, catalog_assets=None)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("missing bundled catalog assets", result.stderr)
        # Nothing was packed: no archive, no manifest.
        self.assertFalse(
            (out / f"eukhe-9.9.9-{HOST_ARCHIVE_PLATFORM}.tar.gz").exists())
        self.assertFalse((out / "manifest.json").exists())

    def test_packers_never_ship_generated_skill_caches(self):
        cache = self.repo.root / "skills" / "__pycache__"
        cache.mkdir()
        (cache / "skill.cpython-311.pyc").write_bytes(b"generated bytecode")
        (self.repo.root / "skills" / "stale.pyc").write_bytes(b"generated bytecode")
        assembled = self.repo.assemble(self.tmp / "assemble-caches", catalog_assets=self.assets)
        self.assertEqual(assembled.returncode, 0, assembled.stderr)
        archive = self.tmp / "assemble-caches" / f"eukhe-9.9.9-{HOST_ARCHIVE_PLATFORM}.tar.gz"
        with tarfile.open(archive) as tar:
            self.assertFalse(any("__pycache__" in name or name.endswith(".pyc") for name in tar.getnames()))
        poisoned = self.tmp / "poisoned"
        poisoned.mkdir()
        shutil.copy2(archive, poisoned / archive.name)
        with tarfile.open(poisoned / archive.name) as original:
            items = [(member, original.extractfile(member).read() if member.isfile() else None)
                     for member in original.getmembers()]
        with tarfile.open(poisoned / archive.name, "w:gz") as bad:
            for member, payload in items:
                bad.addfile(member, io.BytesIO(payload) if payload is not None else None)
            extra = tarfile.TarInfo("skills/__pycache__/skill.cpython-311.pyc")
            extra.size = 1
            bad.addfile(extra, io.BytesIO(b"x"))
        checked = run_cli(VERIFIER, ["--dist-dir", str(poisoned), "--version", "9.9.9",
                                     "--target", HOST_TARGET])
        self.assertNotEqual(checked.returncode, 0)
        self.assertIn("development cache entry", checked.stderr)
        args = ["--root", str(self.repo.root), "--version", "9.9.9",
                "--binary", str(self.repo.binary),
                "--decoder", str(self.repo.decoder), "--skip-build",
                "--catalog-assets", str(self.assets),
                "--out-dir", str(self.tmp / "package-caches")]
        packaged = run_cli(PACKER, args)
        self.assertEqual(packaged.returncode, 0, packaged.stderr)
        staged = self.tmp / "package-caches" / "eukhe-9.9.9-linux-x64" / "skills"
        self.assertFalse(any("__pycache__" in str(path) or path.suffix == ".pyc"
                             for path in staged.rglob("*")))

    def test_packer_fails_on_invalid_assets(self):
        cases = {
            "corrupt-json": "{\n",
            "wrong-version": json.dumps({"schemaVersion": 2, "models": []}),
        }
        for label, models_body in cases.items():
            bad = self.tmp / f"assets-{label}"
            bad.mkdir()
            (bad / "models.bundled.json").write_text(models_body)
            result = self.repo.assemble(self.tmp / f"dist-{label}", catalog_assets=bad)
            self.assertNotEqual(result.returncode, 0, label)
            self.assertIn("Invalid bundled", result.stderr, label)
        # Under-minimum counts fail even with a well-formed envelope.
        small = self.tmp / "assets-small"
        small.mkdir()
        (small / "models.bundled.json").write_text(
            json.dumps({"schemaVersion": 1, "models": []}))
        result = self.repo.assemble(self.tmp / "dist-small", catalog_assets=small)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("transport tuples", result.stderr)
        # A missing asset fails too.
        empty = self.tmp / "assets-empty"
        empty.mkdir()
        result = self.repo.assemble(self.tmp / "dist-empty", catalog_assets=empty)
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("Missing bundled catalog asset", result.stderr)

    def test_assets_land_in_the_release_tarball(self):
        out = self.tmp / "dist"
        result = self.repo.assemble(out, catalog_assets=self.assets)
        self.assertEqual(result.returncode, 0, result.stderr)
        self.assertIn("bundled catalog assets", result.stdout)
        archive = out / f"eukhe-9.9.9-{HOST_ARCHIVE_PLATFORM}.tar.gz"
        self.assertTrue(archive.is_file())
        with tarfile.open(archive) as tar:
            names = tar.getnames()
            self.assertIn("models.bundled.json", names)
            # The staged asset is byte-identical to the generated one.
            member = tar.extractfile("models.bundled.json")
            self.assertEqual(member.read(),
                             (self.assets / "models.bundled.json").read_bytes())
        # The full end-to-end verifier (payload shape, checksums, manifest,
        # extracted catalog assets, livecheck) passes on the synthetic tree.
        verify = run_cli(VERIFIER, ["--dist-dir", str(out), "--version", "9.9.9",
                                   "--target", HOST_TARGET])
        self.assertEqual(verify.returncode, 0, verify.stderr)
        self.assertIn("catalog assets", verify.stdout)

    def test_verifier_rejects_unsafe_tar_members(self):
        """Each unsafe member is rejected before extraction writes it: a
        `..` path that passes the top-level payload check (it starts with
        skills/) would otherwise land outside the scratch directory, and a
        device or FIFO member would be written as a plain file."""
        out = self.tmp / "dist-unsafe"
        result = self.repo.assemble(out, catalog_assets=self.assets)
        self.assertEqual(result.returncode, 0, result.stderr)
        archive_name = f"eukhe-9.9.9-{HOST_ARCHIVE_PLATFORM}.tar.gz"
        with tarfile.open(out / archive_name) as original:
            items = [(member, original.extractfile(member).read() if member.isfile() else None)
                     for member in original.getmembers()]
        manifest = json.loads((out / "manifest.json").read_text())
        cases = {
            "skills/../../escaped": (tarfile.REGTYPE, "not a relative in-tree path"),
            "skills/fifo": (tarfile.FIFOTYPE, "not a regular file or directory"),
        }
        for name, (member_type, error) in cases.items():
            case_dir = self.tmp / f"unsafe-{member_type.decode()}"
            case_dir.mkdir()
            with tarfile.open(case_dir / archive_name, "w:gz") as bad:
                for member, payload in items:
                    bad.addfile(member, io.BytesIO(payload) if payload is not None else None)
                extra = tarfile.TarInfo(name)
                extra.type = member_type
                extra.size = 1 if member_type == tarfile.REGTYPE else 0
                bad.addfile(extra, io.BytesIO(b"x") if member_type == tarfile.REGTYPE else None)
            digest = hashlib.sha256((case_dir / archive_name).read_bytes()).hexdigest()
            (case_dir / "SHA256SUMS").write_text(f"{digest}  {archive_name}\n")
            for binary in manifest["binaries"]:
                binary["sha256"] = digest
            (case_dir / "manifest.json").write_text(json.dumps(manifest))
            # The scratch dir is tmp_root/eukhe-verify-*, so the `..`
            # member would resolve to tmp_root/escaped.
            tmp_root = case_dir / "tmp"
            tmp_root.mkdir()
            checked = run_cli(VERIFIER, ["--dist-dir", str(case_dir), "--version", "9.9.9",
                                         "--target", HOST_TARGET],
                              env_extra={"TMPDIR": str(tmp_root)})
            self.assertNotEqual(checked.returncode, 0, name)
            self.assertIn(error, checked.stderr, name)
            self.assertEqual(list(case_dir.rglob("escaped")), [], name)

    def test_kernel_packer_archive_is_reproducible(self):
        """Two packs of the same input are byte-identical: fixed member
        metadata and a zero gzip mtime, even when packed seconds apart."""
        archives = []
        for run in ("first", "second"):
            out = self.tmp / f"reproducible-{run}"
            packaged = run_cli(PACKER, ["--root", str(self.repo.root), "--version", "9.9.9",
                                        "--binary", str(self.repo.binary),
                                        "--decoder", str(self.repo.decoder), "--skip-build",
                                        "--catalog-assets", str(self.assets),
                                        "--out-dir", str(out)])
            self.assertEqual(packaged.returncode, 0, packaged.stderr)
            archives.append((out / "eukhe-9.9.9-linux-x64.tar.gz").read_bytes())
            time.sleep(1.1)
        self.assertEqual(archives[0], archives[1])

    def test_kernel_packer_gates_the_same_assets(self):
        # package_release.py (the exe-adjacent kernel packaging) fails without
        # assets and ships them beside the binary when they are valid.
        args = ["--root", str(self.repo.root), "--version", "9.9.9",
                "--binary", str(self.repo.binary), "--decoder", str(self.repo.decoder),
                "--skip-build", "--out-dir", str(self.tmp / "release-package")]
        without = run_cli(PACKER, args)
        self.assertNotEqual(without.returncode, 0)
        self.assertIn("missing bundled catalog assets", without.stderr)
        with_assets = run_cli(PACKER, [*args, "--catalog-assets", str(self.assets)])
        self.assertEqual(with_assets.returncode, 0, with_assets.stderr)
        staged = self.tmp / "release-package" / "eukhe-9.9.9-linux-x64"
        self.assertTrue((staged / "models.bundled.json").is_file())

    def test_kernel_packer_rejects_decoder_leak(self):
        leaked = self.repo.root / "rlm" / "leak.debug.gz"
        leaked.write_bytes(b"decoder-like payload")
        out = self.tmp / "release-package-leak"
        result = run_cli(PACKER, ["--root", str(self.repo.root), "--version", "9.9.9",
                                  "--binary", str(self.repo.binary),
                                  "--decoder", str(self.repo.decoder), "--out-dir", str(out),
                                  "--catalog-assets", str(self.assets)])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("decoder-like sidecar", result.stderr)
        self.assertFalse(list(out.glob("*.tar.gz")))

    def test_kernel_packer_requires_decoder_for_explicit_linux_binary(self):
        result = run_cli(PACKER, ["--root", str(self.repo.root), "--version", "9.9.9",
                                  "--binary", str(self.repo.binary),
                                  "--out-dir", str(self.tmp / "release-package-raw"),
                                  "--catalog-assets", str(self.assets)])
        self.assertNotEqual(result.returncode, 0)
        self.assertIn("requires --decoder", result.stderr)

    def test_linux_assembler_requires_split_binary_and_decoder(self):
        base = ["--repo-root", str(self.repo.root), "--version", "9.9.9",
                "--target", HOST_TARGET, "--runtime-dir", str(self.repo.root / "runtime"),
                "--catalog-assets", str(self.assets), "--out-dir", str(self.tmp / "invalid")]
        wrong_dir = self.tmp / "wrong-decoder"
        wrong_dir.mkdir()
        wrong_source = wrong_dir / "wrong.c"
        wrong_source.write_text('int main(void) { return 17; }\n')
        wrong_raw = wrong_dir / "cargo-eukhe"
        subprocess.run(["gcc", "-g", "-Wl,--build-id", "-o", str(wrong_raw),
                        str(wrong_source)], check=True)
        split = run_cli(SCRIPTS_DIR / "split_debug.py", [
            "--binary", str(wrong_raw), "--shipped", str(wrong_dir / "eukhe"),
            "--out", str(wrong_dir), "--version", "9.9.9", "--target", HOST_TARGET])
        self.assertEqual(split.returncode, 0, split.stderr)
        wrong_decoder = wrong_dir / self.repo.decoder.name
        for flags, error in (([], "requires explicit --binary"),
                             (["--binary", str(self.repo.binary)], "requires explicit --binary"),
                             (["--binary", str(self.repo.raw_binary),
                               "--decoder", str(self.repo.decoder)], "still has DWARF"),
                             (["--binary", str(self.repo.binary),
                               "--decoder", str(wrong_decoder)], "build ID does not match")):
            result = run_cli(ASSEMBLER, [*base, *flags])
            self.assertNotEqual(result.returncode, 0, flags)
            self.assertIn(error, result.stderr)
        self.assertFalse(list((self.tmp / "invalid").glob("*.tar.gz")))


if __name__ == "__main__":
    unittest.main(verbosity=2)
