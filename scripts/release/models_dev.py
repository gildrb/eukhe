#!/usr/bin/env python3
"""Eukhe's bundled model catalog, made from a pinned models.dev snapshot.

models.dev (https://github.com/anomalyco/models.dev, MIT) publishes model
facts per host: limits, costs, modalities and reasoning controls. Eukhe
ships a pinned projection of it and maps it to its own catalog entries
(the strict `catalog.v1` shape `models.bundled.json` carries). Three files
under crates/eukhe-models/catalog/:

  models-dev.json      the snapshot: models.dev's v1 API (`api.json`) at one
                       commit, cut to the providers the overrides name and
                       to the fields this mapping reads
  models-dev.pin.json  repository, commit, commit date and the snapshot's
                       sha256; `generate` refuses a snapshot that does not
                       match it
  overrides.json       what models.dev cannot say: each provider's routes
                       (Eukhe provider id, wire API and base URL), the
                       per-model corrections, and the ids to leave out

Nothing here runs at runtime: `generate` is a pure function of the three
files, and `refresh` is the one step that reads models.dev, at a commit.

The mapping, per models.dev provider model (see `map_model`):

  kept       `tool_call` true, `status` not `deprecated`, no specialized
             `type` (image, embedding, ...), and a route for its SDK
  id         the models.dev id, rewritten by the route (`stripPrefix`,
             `dotsToDashes`)
  api        the route's wire API: the first route whose `npm` is the
  baseUrl    model's per-model SDK (`provider.npm`; `null`: none) and whose
             `idPrefix` matches; no route, no entry
  name       `name`
  reasoning  `reasoning`
  input      text, plus image when `modalities.input` lists it
  cost       `cost.input/output/cache_read/cache_write` (USD per million
             tokens; absent: 0)
  contextWindow  `limit.context`
  maxTokens      `limit.output` (absent: `limit.context`)
  thinkingLevelMap  from `reasoning_options` (reasoning models only; no
             map: the default ladder, off..high):
             - effort list: minimal..high it lists keep the wire API's own
               form, the others are `null` (not offered); xhigh and max map
               to themselves when listed; off is `"none"` when the list has
               `none`, offered (the API's own off) with a `toggle`, else
               `null` (no off: the lowest offered level runs)
             - budget without effort: the default ladder; off is `null`
               when the budget cannot reach zero (`min` > 0) and nothing
               turns thinking off (no `toggle`, and an API where thinking
               is not opt-in: not `anthropic-messages` or
               `bedrock-converse-stream`)
             - toggle alone: the default ladder
             - no controls (always on): every level `null`, so no level is
               offered and no reasoning field is sent
  compat     none from models.dev (the quirks rulebook decides it per
             host); only from overrides

The bundle carries only models the compiled catalog lacks (the eukhe-ai
provider data under crates/eukhe-ai/src/providers/data): a compiled model
keeps its compiled entry everywhere, and models.dev fills in the rest.
Then overrides.json `models["<provider>/<id>"]` replaces or removes fields
(`null` deletes a field; `{"skip": true}` drops the entry).

Usage:
    python3 scripts/release/models_dev.py generate [--out FILE]
    python3 scripts/release/models_dev.py check
    python3 scripts/release/models_dev.py refresh [--commit REF]

`check` fails unless the committed catalog fixture
(crates/eukhe-models/tests/fixtures/catalog.v1.json) is what `generate`
writes. `refresh` needs git and bun: it checks models.dev out at REF
(default main), builds its v1 API with the repository's own generator,
projects it and rewrites the snapshot and the pin. Review the diff, then
regenerate the fixture (scripts/generate-catalog-fixture.py) and commit.
"""

from __future__ import annotations

import argparse
import hashlib
import json
import re
import subprocess
import sys
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent.parent
CATALOG_DIR = ROOT / "crates" / "eukhe-models" / "catalog"
SNAPSHOT = CATALOG_DIR / "models-dev.json"
PIN = CATALOG_DIR / "models-dev.pin.json"
OVERRIDES = CATALOG_DIR / "overrides.json"
COMPILED_DATA = ROOT / "crates" / "eukhe-ai" / "src" / "providers" / "data"
FIXTURE = ROOT / "crates" / "eukhe-models" / "tests" / "fixtures" / "catalog.v1.json"
REPOSITORY = "anomalyco/models.dev"
REPOSITORY_URL = f"https://github.com/{REPOSITORY}.git"

# The levels of an Eukhe thinking ladder, weakest first, and the ones the
# default reasoning ladder offers without an entry in the map.
DEFAULT_LADDER = ("minimal", "low", "medium", "high")
EXTRA_LEVELS = ("xhigh", "max")
# Wire APIs where a request without a thinking block does not think: off is
# always available there, whatever controls the host lists.
OPT_IN_THINKING_APIS = {"anthropic-messages", "bedrock-converse-stream"}
# Specialized models.dev types are no chat models.
CHAT_TYPES = {None, "chat"}

# The snapshot keeps what the mapping reads, and the name.
PROVIDER_FIELDS = ("name", "npm", "api")
MODEL_FIELDS = (
    "name", "type", "status", "reasoning", "reasoning_options", "tool_call",
    "modalities", "limit", "cost", "provider",
)
COST_FIELDS = ("input", "output", "cache_read", "cache_write")


def fail(message: str) -> None:
    print(f"error: {message}", file=sys.stderr)
    sys.exit(1)


def canonical_json(value) -> str:
    """The committed form: sorted keys, 1-space indent, trailing newline."""
    return json.dumps(value, indent=1, sort_keys=True, ensure_ascii=False) + "\n"


def sha256_text(text: str) -> str:
    return hashlib.sha256(text.encode("utf-8")).hexdigest()


# --------------------------------------------------------------------------
# Inputs
# --------------------------------------------------------------------------

def load_overrides(path: Path = OVERRIDES) -> dict:
    try:
        overrides = json.loads(Path(path).read_text())
    except (OSError, ValueError) as error:
        fail(f"cannot read {path}: {error}")
    if not isinstance(overrides, dict) or set(overrides) - {"providers", "models"}:
        fail(f"{path}: expected the keys providers and models")
    for provider, spec in overrides.get("providers", {}).items():
        if set(spec) - {"modelsDev", "routes", "include"}:
            fail(f"{path}: provider {provider}: unknown keys {sorted(set(spec) - {'modelsDev', 'routes', 'include'})}")
        if not isinstance(spec.get("modelsDev"), str) or not spec.get("routes"):
            fail(f"{path}: provider {provider} needs modelsDev and routes")
        for route in spec["routes"]:
            unknown = set(route) - {"npm", "idPrefix", "api", "baseUrl", "stripPrefix", "dotsToDashes"}
            if unknown or not isinstance(route.get("api"), str) or not isinstance(route.get("baseUrl"), str):
                fail(f"{path}: provider {provider}: a route needs api and baseUrl "
                     f"(unknown keys {sorted(unknown)})")
    return overrides


def load_snapshot(snapshot: Path = SNAPSHOT, pin: Path = PIN) -> dict:
    """The snapshot, refused unless its bytes match the pin's sha256."""
    try:
        text = Path(snapshot).read_text()
        pinned = json.loads(Path(pin).read_text())
    except (OSError, ValueError) as error:
        fail(f"cannot read the models.dev snapshot: {error}")
    if set(pinned) != {"repository", "commit", "date", "sha256"}:
        fail(f"{pin}: expected the keys repository, commit, date, sha256")
    actual = sha256_text(text)
    if actual != pinned["sha256"]:
        fail(f"{snapshot}: sha256 {actual} does not match the pin {pinned['sha256']}; "
             "run `python3 scripts/release/models_dev.py refresh` to move the pin")
    return json.loads(text)


# --------------------------------------------------------------------------
# The mapping
# --------------------------------------------------------------------------

def route_for(spec: dict, model_id: str, model: dict) -> dict | None:
    npm = (model.get("provider") or {}).get("npm")
    for route in spec["routes"]:
        if "npm" in route and route["npm"] != npm:
            continue
        if "idPrefix" in route and not model_id.startswith(route["idPrefix"]):
            continue
        return route
    return None


def route_id(route: dict, model_id: str) -> str:
    prefix = route.get("stripPrefix")
    if prefix and model_id.startswith(prefix):
        model_id = model_id[len(prefix):]
    if route.get("dotsToDashes"):
        model_id = model_id.replace(".", "-")
    return model_id


def thinking_level_map(model: dict, api: str) -> dict | None:
    """Eukhe's ladder for a reasoning model's models.dev controls (module
    docs). `None`: the default ladder."""
    if model.get("reasoning") is not True:
        return None
    options = {option.get("type"): option for option in model.get("reasoning_options") or []}
    if not options:
        # Always on, no caller control: no level to offer, no field to send.
        return {level: None for level in ("off", *DEFAULT_LADDER)}
    effort = options.get("effort", {}).get("values")
    toggle = "toggle" in options
    if not effort:
        budget = options.get("budget_tokens")
        # A budget that cannot go to zero, with no on/off control: no off.
        if budget is not None and not toggle and budget.get("min", 0) > 0 \
                and api not in OPT_IN_THINKING_APIS:
            return {"off": None}
        return None
    ladder: dict = {}
    for level in DEFAULT_LADDER:
        if level not in effort:
            ladder[level] = None
    for level in EXTRA_LEVELS:
        if level in effort:
            ladder[level] = level
    if "none" in effort:
        ladder["off"] = "none"
    elif not toggle:
        ladder["off"] = None
    return ladder


def map_model(provider: str, route: dict, model_id: str, model: dict) -> dict:
    limit = model.get("limit") or {}
    cost = model.get("cost") or {}
    inputs = (model.get("modalities") or {}).get("input") or []
    entry = {
        "id": route_id(route, model_id),
        "name": model.get("name") or model_id,
        "api": route["api"],
        "provider": provider,
        "baseUrl": route["baseUrl"],
        "reasoning": model.get("reasoning") is True,
        "input": ["text", "image"] if "image" in inputs else ["text"],
        "cost": {
            "input": cost.get("input", 0),
            "output": cost.get("output", 0),
            "cacheRead": cost.get("cache_read", 0),
            "cacheWrite": cost.get("cache_write", 0),
        },
        "contextWindow": limit.get("context"),
        "maxTokens": limit.get("output") or limit.get("context"),
    }
    ladder = thinking_level_map(model, route["api"])
    if ladder is not None:
        entry["thinkingLevelMap"] = ladder
    return entry


def kept(model: dict) -> bool:
    return (model.get("tool_call") is True and model.get("status") != "deprecated"
            and model.get("type") in CHAT_TYPES)


def apply_override(entry: dict, override: dict) -> dict | None:
    if override.get("skip") is True:
        return None
    for key, value in override.items():
        if value is None:
            entry.pop(key, None)
        else:
            entry[key] = value
    return entry


def load_compiled(directory: Path = COMPILED_DATA) -> set:
    """The `(provider, id)` of every compiled model (the eukhe-ai provider
    data the binary embeds)."""
    compiled = set()
    for path in sorted(Path(directory).glob("*.json")):
        for group in json.loads(path.read_text()).values():
            for model in group.values():
                compiled.add((model["provider"], model["id"]))
    if not compiled:
        fail(f"no compiled model data under {directory}")
    return compiled


def generate_catalog(snapshot: dict, overrides: dict, compiled: set) -> dict:
    """The `catalog.v1` payload: every mapped entry the compiled catalog
    lacks, sorted by (provider, id)."""
    models = []
    seen: set = set()
    model_overrides = overrides.get("models", {})
    used: set = set()
    for provider, spec in overrides["providers"].items():
        source = snapshot.get(spec["modelsDev"])
        if source is None:
            fail(f"the snapshot has no models.dev provider {spec['modelsDev']} (for {provider})")
        include = re.compile(spec["include"]) if "include" in spec else None
        for model_id, model in source["models"].items():
            if not kept(model) or (include and not include.search(model_id)):
                continue
            route = route_for(spec, model_id, model)
            if route is None:
                continue
            entry = map_model(provider, route, model_id, model)
            if (provider, entry["id"]) in compiled:
                continue
            key = f"{provider}/{entry['id']}"
            if key in model_overrides:
                used.add(key)
                entry = apply_override(entry, model_overrides[key])
                if entry is None:
                    continue
            if (provider, entry["id"]) in seen:
                fail(f"two models.dev models map to {key}")
            seen.add((provider, entry["id"]))
            models.append(entry)
    stale = sorted(set(model_overrides) - used)
    if stale:
        fail("overrides name models the bundle does not carry (absent from the "
             f"snapshot, or compiled): {', '.join(stale)}")
    models.sort(key=lambda entry: (entry["provider"], entry["id"]))
    return {"schemaVersion": 1, "models": models}


def catalog_text(snapshot: dict, overrides: dict, compiled: set) -> str:
    catalog = generate_catalog(snapshot, overrides, compiled)
    return json.dumps(catalog, indent=2, ensure_ascii=False) + "\n"


def bundled_catalog_text() -> str:
    """The bundled models asset of this checkout."""
    return catalog_text(load_snapshot(), load_overrides(), load_compiled())


# --------------------------------------------------------------------------
# Refresh: build models.dev's v1 API at a commit and project it
# --------------------------------------------------------------------------

# models.dev's own generator (packages/core) builds the v1 API; the default
# model-type filter is what https://models.dev/api.json serves.
GENERATOR = """\
import {{ generateCatalog, filterCatalogByModelType }} from "./packages/core/src/index.ts";
const catalog = filterCatalogByModelType(await generateCatalog(process.cwd()), "default");
await Bun.write({out!r}, JSON.stringify(catalog.providers));
"""


def project(api: dict, keys) -> dict:
    snapshot = {}
    for key in sorted(keys):
        provider = api.get(key)
        if provider is None:
            fail(f"models.dev has no provider {key}")
        projected = {field: provider[field] for field in PROVIDER_FIELDS if field in provider}
        projected["models"] = {
            model_id: {field: model[field] for field in MODEL_FIELDS if field in model}
            for model_id, model in sorted(provider["models"].items())
        }
        for model in projected["models"].values():
            if "cost" in model:
                model["cost"] = {field: model["cost"][field]
                                 for field in COST_FIELDS if field in model["cost"]}
            if "modalities" in model:
                model["modalities"] = {"input": model["modalities"].get("input", [])}
        snapshot[key] = projected
    return snapshot


def run(command: list, cwd: Path) -> str:
    result = subprocess.run(command, cwd=cwd, capture_output=True, text=True)
    if result.returncode != 0:
        fail(f"{' '.join(command)} failed: {result.stderr.strip()[-2000:]}")
    return result.stdout.strip()


def refresh(ref: str) -> dict:
    overrides = load_overrides()
    keys = {spec["modelsDev"] for spec in overrides["providers"].values()}
    with tempfile.TemporaryDirectory() as scratch:
        checkout = Path(scratch) / "models.dev"
        run(["git", "init", "-q", str(checkout)], Path(scratch))
        run(["git", "fetch", "-q", "--depth", "1", REPOSITORY_URL, ref], checkout)
        run(["git", "checkout", "-q", "FETCH_HEAD"], checkout)
        commit = run(["git", "rev-parse", "HEAD"], checkout)
        date = run(["git", "show", "-s", "--format=%cI", "HEAD"], checkout)
        run(["bun", "install", "--frozen-lockfile"], checkout)
        out = Path(scratch) / "api.json"
        (checkout / "eukhe-generate.ts").write_text(GENERATOR.format(out=str(out)))
        run(["bun", "./eukhe-generate.ts"], checkout)
        api = json.loads(out.read_text())
    text = canonical_json(project(api, keys))
    snapshot = json.loads(text)
    catalog = generate_catalog(snapshot, overrides, load_compiled())
    SNAPSHOT.write_text(text)
    pin = {"repository": REPOSITORY, "commit": commit, "date": date, "sha256": sha256_text(text)}
    PIN.write_text(json.dumps(pin, indent=2) + "\n")
    return {"pin": pin, "models": len(catalog["models"])}


def main(argv=None) -> int:
    parser = argparse.ArgumentParser(description=__doc__.splitlines()[0])
    parser.add_argument("command", choices=("generate", "check", "refresh"))
    parser.add_argument("--out", type=Path, default=None,
                        help="generate: write the catalog here (default: stdout)")
    parser.add_argument("--commit", default="main",
                        help="refresh: the models.dev commit or ref (default: main)")
    args = parser.parse_args(argv)
    if args.command == "refresh":
        print(json.dumps(refresh(args.commit), indent=2))
        return 0
    text = bundled_catalog_text()
    if args.command == "check":
        if not FIXTURE.is_file() or FIXTURE.read_text() != text:
            fail(f"{FIXTURE} is not the generated catalog; run "
                 "`python3 scripts/generate-catalog-fixture.py`")
        print(json.dumps({"models": len(json.loads(text)["models"])}))
    elif args.out is None:
        sys.stdout.write(text)
    else:
        args.out.write_text(text)
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
