#!/usr/bin/env python3
"""Puts Paper Mono's release files in public/fonts, unmodified (no subsetting,
no renaming: the OFL's Reserved Font Name question never arises): the two
weights the site sets (Regular 400, Bold 700) and the release's OFL.txt. The
checksums are those files at the pinned release; a new release changes them
here and `?v=` in src/render.tsx.

Usage (in site/): python3 scripts/fonts.py
"""

from __future__ import annotations

import hashlib
import shutil
import subprocess
import sys
import tempfile
import zipfile
from pathlib import Path

SITE = Path(__file__).resolve().parents[1]
VERSION = "v1.000"
CHECKSUMS = {
    "public/fonts/PaperMono-Regular.woff2": "ebfbaa0f177a172a207b38dc5708f6e0b648f75cd3fa523d5097380fa2a707f0",
    "public/fonts/PaperMono-Bold.woff2": "2a7bfa7f29e15ab37a463bae8d7a953cdf8728664a77b759e211f58ab07be258",
    "public/fonts/OFL.txt": "ae8bcaf5a046be7e096b5710a8532cdaa5a299462e182752b805dcfa44370e4c",
}


def main() -> int:
    archive = f"paper-mono-{VERSION}.zip"
    with tempfile.TemporaryDirectory() as work:
        download = ["gh", "release", "download", VERSION, "-R", "paper-design/paper-mono", "-p", archive, "-D", work]
        code = subprocess.run(download).returncode
        if code:
            return code
        with zipfile.ZipFile(Path(work) / archive) as release_zip:
            release_zip.extractall(work)
        release = Path(work) / f"paper-mono-{VERSION}"
        for source in ("fonts/webfonts/PaperMono-Regular.woff2", "fonts/webfonts/PaperMono-Bold.woff2", "OFL.txt"):
            shutil.copyfile(release / source, SITE / "public" / "fonts" / Path(source).name)
    failed = 0
    for path, checksum in CHECKSUMS.items():
        ok = hashlib.sha256((SITE / path).read_bytes()).hexdigest() == checksum
        print(f"{path}: {'OK' if ok else 'FAILED'}")
        failed += not ok
    if failed:
        print(f"WARNING: {failed} computed checksum{'s' if failed > 1 else ''} did NOT match", file=sys.stderr)
        return 1
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
