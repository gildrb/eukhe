#!/usr/bin/env python3
"""Refresh the catalog fixture (crates/eukhe-models/tests/fixtures/catalog.v1.json).

The fixture is the bundled models asset itself: the pinned models.dev
snapshot (crates/eukhe-models/catalog/models-dev.json) mapped through
crates/eukhe-models/catalog/overrides.json by scripts/release/models_dev.py,
the same bytes `bundle_catalog.py generate` writes to models.bundled.json.
The Rust suites parse this committed copy, so they run against the shipped
catalog hermetically; scripts/release/test_models_dev.py fails when it
drifts from the snapshot and the overrides.

Usage:
  python3 scripts/generate-catalog-fixture.py
"""

from __future__ import annotations

import json
import sys
from pathlib import Path

REPO = Path(__file__).resolve().parent.parent
sys.path.insert(0, str(REPO / "scripts" / "release"))
import models_dev  # noqa: E402


def main() -> None:
    text = models_dev.bundled_catalog_text()
    models_dev.FIXTURE.write_text(text)
    models = json.loads(text)["models"]
    providers = {model["provider"] for model in models}
    print(f"{models_dev.FIXTURE}: {len(models)} models, {len(providers)} providers")


if __name__ == "__main__":
    main()
