#!/usr/bin/env python3
"""Tests of xz_archives.py: each twin holds the same tar as its .tar.gz.

Run: python3 scripts/release/test_xz_archives.py  (needs xz >= 5.4)
"""

from __future__ import annotations

import gzip
import io
import subprocess
import sys
import tarfile
import tempfile
import unittest
from pathlib import Path

HERE = Path(__file__).resolve().parent
SCRIPT = HERE / "xz_archives.py"


def tar_bytes() -> bytes:
    out = io.BytesIO()
    with tarfile.open(fileobj=out, mode="w", format=tarfile.PAX_FORMAT) as archive:
        for name, data in (("eukhe", b"\x7fELF" + bytes(range(256)) * 64), ("LICENSE", b"MIT\n")):
            info = tarfile.TarInfo(name)
            info.size = len(data)
            archive.addfile(info, io.BytesIO(data))
    return out.getvalue()


class XzTwinTests(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp(prefix="eukhe-xz-test-"))

    def run_script(self, *names: str) -> subprocess.CompletedProcess:
        return subprocess.run([sys.executable, str(SCRIPT), *names],
                              capture_output=True, text=True, check=False)

    def test_each_twin_unpacks_to_the_tar_of_its_gz(self):
        tar = tar_bytes()
        names = []
        for alias in ("linux-x64", "linux-arm64", "darwin-arm64"):
            gz = self.tmp / f"eukhe-9.9.9-{alias}.tar.gz"
            gz.write_bytes(gzip.compress(tar, mtime=0))
            names.append(str(gz))
        result = self.run_script(*names)
        self.assertEqual(result.returncode, 0, result.stderr)
        listed = [line.split()[1] for line in result.stdout.splitlines()]
        self.assertEqual(listed, [Path(n).name.removesuffix(".gz") + ".xz" for n in names])
        for name in listed:
            back = subprocess.run(["xz", "-d", "--stdout", str(self.tmp / name)],
                                  capture_output=True, check=True).stdout
            self.assertEqual(back, tar, name)

    def test_a_file_that_is_no_release_archive_is_refused(self):
        other = self.tmp / "eukhe-9.9.9-windows-x64.tar.gz"
        other.write_bytes(gzip.compress(tar_bytes(), mtime=0))
        result = self.run_script(str(other))
        self.assertEqual(result.returncode, 1)
        self.assertIn("is not a release archive", result.stderr)
        self.assertFalse(other.with_name(other.name.removesuffix(".gz") + ".xz").exists())


if __name__ == "__main__":
    unittest.main()
