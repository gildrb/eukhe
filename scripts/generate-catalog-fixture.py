#!/usr/bin/env python3
"""Refresh the catalog parity fixture (tests/fixtures/catalog.v1.json).

The fixture is a byte-faithful snapshot of the real catalog repo
(PrimeIntellect-ai/prime-agent-catalog, models/catalog.v1.json). The
published payload already IS the catalog aggregate `createModelCatalog`
builds from it (packages/ai/src/model-catalog.ts semantics): schemaVersion
1, headers stripped, prime-inference excluded (it is fetched live),
entries sorted by (provider, id). CI parses this committed snapshot so the
parity verifier runs against real data at real scale, hermetically.

The default mode fetches models/catalog.v1.json at the commit pinned in
scripts/release/catalog-pin.json with the release bundler's guards (public
repo; optional GITHUB_TOKEN / PRIME_CATALOG_REPO_TOKEN Bearer; aborts after
5 s, refuses redirects, caps responses at MAX_REMOTE_CATALOG_BYTES, fails
unless the body matches the pinned sha256 — the same fetch
scripts/release/bundle_catalog.py uses); `--catalog-dir <prime-agent-catalog>`
reads a local checkout instead, so the refresh also works offline.

Usage:
  python3 scripts/generate-catalog-fixture.py
  python3 scripts/generate-catalog-fixture.py --catalog-dir <prime-agent-catalog>
"""

from __future__ import annotations

import argparse
import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
FIXTURE = REPO / "crates/eukhe-models/tests/fixtures/catalog.v1.json"

sys.path.insert(0, str(REPO / "scripts" / "release"))
from bundle_catalog import (  # noqa: E402
    CATALOG_PIN,
    MODELS_SOURCE,
    fail,
    fetch_pinned,
    load_catalog_pin,
    pinned_url,
)


def parse_aggregate(text: str) -> list:
    """The fixture contract: the real catalog payload, aggregate-shaped."""
    catalog = json.loads(text)
    models = catalog["models"]
    if catalog.get("schemaVersion") != 1 or not isinstance(models, list) or not models:
        fail("the payload is not the models/catalog.v1.json aggregate")
    prime_inference = [m for m in models if m.get("provider") == "prime-inference"]
    if prime_inference:
        fail(
            "the catalog aggregate must exclude prime-inference "
            f"({len(prime_inference)} entries present)"
        )
    with_headers = [m for m in models if "headers" in m]
    if with_headers:
        fail(f"catalog entries must not carry headers ({len(with_headers)} do)")
    return models


def main() -> None:
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument(
        "--catalog-dir",
        type=Path,
        default=None,
        help="read models/catalog.v1.json from a local prime-agent-catalog "
        "checkout instead of fetching the pinned catalog commit",
    )
    args = parser.parse_args()

    if args.catalog_dir is not None:
        text = (args.catalog_dir / "models" / "catalog.v1.json").read_text()
        if not text.endswith("\n"):
            text = f"{text}\n"
    else:
        pin = load_catalog_pin(CATALOG_PIN)
        text = fetch_pinned(
            pinned_url(pin["repository"], pin["commit"], MODELS_SOURCE),
            "model", pin["files"][MODELS_SOURCE])
    models = parse_aggregate(text)
    FIXTURE.write_text(text)
    providers = {model["provider"] for model in models}
    print(f"{FIXTURE}: {len(models)} models, {len(providers)} providers")


if __name__ == "__main__":
    main()
