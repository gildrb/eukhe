#!/usr/bin/env python3
"""Generate and validate the bundled catalog asset for eukhe releases.

The asset is the client's no-cold-start layer 2 (spec §3.2):

  models.bundled.json  Eukhe's model catalog ({schemaVersion, models}),
                       mapped from the pinned models.dev snapshot in
                       crates/eukhe-models/catalog (models_dev.py)

It is generated offline at BUILD time from the committed snapshot and its
overrides, and never committed.

Validation (the release packer runs the same functions before packing):
  models  schemaVersion == 1, models is an array, and at least
          MIN_MODEL_TRANSPORT_TUPLES distinct (provider, api, baseUrl) tuples

Usage:
    python3 .github/scripts/release/bundle_catalog.py generate [--out DIR] [--allow-small-fixture]
    python3 .github/scripts/release/bundle_catalog.py verify [--out DIR] [--allow-small-fixture]
"""

from __future__ import annotations

import argparse
import json
import math
import sys
from pathlib import Path

import models_dev  # same release-scripts directory

ROOT = Path(__file__).resolve().parents[3]

# The bundled asset names (spec §3.2; TS bundledCatalogFiles).
BUNDLED_CATALOG_FILES = ("models.bundled.json",)

# Release-gate minimum (spec §3.2/§3.9): the models asset carries the
# models.dev models the compiled catalog lacks, over 29 distinct transport
# tuples at the pinned snapshot (the gate catches a truncated asset).
MIN_MODEL_TRANSPORT_TUPLES = 20


def fail(message: str) -> None:
    print(f"error: {message}", file=sys.stderr)
    sys.exit(1)


# --------------------------------------------------------------------------
# Validation (imported by the release packer: assemble_artifacts.py,
# package_release.py, verify_release.py)
# --------------------------------------------------------------------------

# The runtime's strict model entry schema (CatalogModelSchema:
# deny_unknown_fields, TS strictObject): one unknown key makes the strict
# parse drop the WHOLE asset, so the packaging gate rejects it too.
_MODEL_ENTRY_KEYS = {
    "id", "name", "api", "provider", "baseUrl", "reasoning", "thinkingLevelMap",
    "input", "cost", "contextWindow", "maxTokens", "featured", "compat",
}


def _is_finite_number(value) -> bool:
    return isinstance(value, (int, float)) and not isinstance(value, bool) \
        and math.isfinite(value)


def validate_bundled_model_catalog(path: Path, allow_small_fixture: bool = False) -> dict:
    """Gate the bundled model catalog: envelope, per-entry schema, and the
    transport-tuple minimum.

    The per-entry checks mirror the runtime's strict parse_model_catalog
    (schemaVersion 1, Reject): a malformed entry makes the runtime drop the
    WHOLE asset (fail-closed), so the packaging gate enforces the same shape
    here — required bounded strings, boolean reasoning, 1-2 model inputs,
    finite bounded costs, bounded contextWindow/maxTokens, and unique
    (provider, id) pairs. The transport-tuple minimum stays the build gate.
    """
    try:
        catalog = json.loads(Path(path).read_text())
    except (OSError, ValueError) as error:
        fail(f"Invalid bundled model catalog {path}: {error}")
    if not isinstance(catalog, dict) or catalog.get("schemaVersion") != 1 \
            or not isinstance(catalog.get("models"), list):
        fail(f"Invalid bundled model catalog: {path}")
    tuples = set()
    seen_ids = set()
    for index, model in enumerate(catalog["models"]):
        entry = f"model catalog entry [{index}]"
        if not isinstance(model, dict):
            fail(f"Invalid bundled {entry}: entries must be objects")
        unknown = set(model) - _MODEL_ENTRY_KEYS
        if unknown:
            fail(f"Invalid bundled {entry}: unknown keys {sorted(unknown)} "
                 "(the strict runtime schema rejects unknown fields)")
        for key in ("id", "name", "api", "provider"):
            if not isinstance(model.get(key), str) or not model[key]:
                fail(f"Invalid bundled {entry}: {key} must be a non-empty string")
        if len(model["id"]) > 1024 or len(model["name"]) > 1024 \
                or any(ord(ch) < 0x20 for ch in model["id"] + model["name"]):
            fail(f"Invalid bundled {entry}: id/name must be bounded control-free strings")
        if not 1 <= len(model["api"]) <= 128 or not 1 <= len(model["provider"]) <= 128:
            fail(f"Invalid bundled {entry}: api/provider must be 1-128 chars")
        base_url = model.get("baseUrl")
        if not isinstance(base_url, str) or len(base_url) > 2048:
            fail(f"Invalid bundled {entry}: baseUrl must be a string of at most 2048 chars")
        if not isinstance(model.get("reasoning"), bool):
            fail(f"Invalid bundled {entry}: reasoning must be a boolean")
        inputs = model.get("input")
        if not isinstance(inputs, list) or not 1 <= len(inputs) <= 2 \
                or not all(isinstance(item, str) and item in ("text", "image")
                           for item in inputs):
            fail(f"Invalid bundled {entry}: input must be 1-2 of text/image")
        cost = model.get("cost")
        if not isinstance(cost, dict):
            fail(f"Invalid bundled {entry}: cost must be an object")
        for key in ("input", "output", "cacheRead", "cacheWrite"):
            value = cost.get(key)
            if not _is_finite_number(value) or not 0 <= value <= 1_000_000:
                fail(f"Invalid bundled {entry}: cost.{key} must be a number in [0, 1000000]")
        for key in ("contextWindow", "maxTokens"):
            value = model.get(key)
            if not isinstance(value, int) or isinstance(value, bool) \
                    or not 1 <= value <= 100_000_000:
                fail(f"Invalid bundled {entry}: {key} must be an integer in [1, 100000000]")
        if (model["provider"], model["id"]) in seen_ids:
            fail(f"Invalid bundled {entry}: duplicate provider/id pair "
                 f"({model['provider']}, {model['id']})")
        seen_ids.add((model["provider"], model["id"]))
        tuples.add((model["provider"], model["api"], base_url))
    if not allow_small_fixture and len(tuples) < MIN_MODEL_TRANSPORT_TUPLES:
        fail(
            f"Bundled model catalog has {len(tuples)} transport tuples; "
            f"expected at least {MIN_MODEL_TRANSPORT_TUPLES}"
        )
    return {"models": len(catalog["models"]), "transportTuples": len(tuples)}


def validate_bundled_catalog_dir(directory, allow_small_fixture: bool = False) -> dict:
    """Validate the bundled assets in a directory (the release packer gate)."""
    directory = Path(directory)
    for name in BUNDLED_CATALOG_FILES:
        if not (directory / name).is_file():
            fail(f"Missing bundled catalog asset: {directory / name}")
    return {
        "models": validate_bundled_model_catalog(
            directory / "models.bundled.json", allow_small_fixture),
    }


# --------------------------------------------------------------------------
# Generation
# --------------------------------------------------------------------------

def models_body() -> str:
    """The models asset: the pinned models.dev snapshot mapped through its
    overrides (models_dev.py)."""
    return models_dev.bundled_catalog_text()


def generate_bundled_catalog_assets(options) -> dict:
    out_dir = Path(options.out_dir).resolve() if options.out_dir \
        else (ROOT / "target" / "catalog-assets")
    out_dir.mkdir(parents=True, exist_ok=True)
    (out_dir / "models.bundled.json").write_text(models_body())
    result = validate_bundled_catalog_dir(
        out_dir, allow_small_fixture=options.allow_small_fixture)
    result["outDir"] = str(out_dir)
    return result


def parse_args(argv=None) -> argparse.Namespace:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("command", nargs="?", default="generate",
                        choices=("generate", "verify"),
                        help="generate (default) or verify an existing --out dir")
    parser.add_argument("--out", dest="out_dir", default=None,
                        help="asset output directory (default: target/catalog-assets)")
    parser.add_argument("--allow-small-fixture", action="store_true",
                        help="skip the minimum-count gate (smoke fixtures only)")
    return parser.parse_args(argv)


def main(argv=None) -> int:
    args = parse_args(argv)
    out_dir = args.out_dir or (ROOT / "target" / "catalog-assets")
    if args.command == "verify":
        result = validate_bundled_catalog_dir(
            out_dir, allow_small_fixture=args.allow_small_fixture)
        result["outDir"] = str(out_dir)
        print(json.dumps(result, indent=2))
        return 0
    print(json.dumps(generate_bundled_catalog_assets(args), indent=2))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
