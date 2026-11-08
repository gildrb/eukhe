#!/usr/bin/env python3
"""Fixture `migrate`: ~200 legacy `cfg` call sites over 48 modules to migrate to typed `settings`.

The tests are behavioral (each module's describe() with an empty and a full config source), so a
migration that changes a default fails them. The grader re-runs the pristine tests (<data>/hidden/migrate).
"""
import json
import pathlib
import random
import shutil
import subprocess
import sys

ROOT = pathlib.Path(sys.argv[1]).resolve()  # the bench data dir
OUT = ROOT / "fixtures" / "migrate"
HIDDEN = ROOT / "hidden" / "migrate"

DEFAULTS = {
    "db.host": "localhost", "db.port": 5432, "db.name": "app", "db.pool": 5, "db.timeout": 30,
    "cache.ttl": 300, "cache.size": 1024, "cache.enabled": True, "cache.prefix": "app:",
    "mail.host": "smtp.local", "mail.port": 25, "mail.sender": "noreply@app.test", "mail.retries": 3,
    "api.base_url": "http://localhost:8000", "api.token": None, "api.timeout": 10, "api.verify_tls": True,
    "log.level": "info", "log.json": False, "log.file": None,
    "feature.beta": False, "feature.search": True, "feature.export": False, "feature.audit": False,
    "limits.upload": 10, "limits.download": 50, "limits.requests": 100, "limits.jobs": 4,
}
FULL = {
    "db.host": "db.prod", "db.port": 6543, "db.name": "prod", "db.pool": 20, "db.timeout": 5,
    "cache.ttl": 60, "cache.size": 4096, "cache.enabled": False, "cache.prefix": "p:",
    "mail.host": "smtp.prod", "mail.port": 587, "mail.sender": "ops@prod.test", "mail.retries": 7,
    "api.base_url": "https://api.prod", "api.token": "s3cret", "api.timeout": 3, "api.verify_tls": False,
    "log.level": "warning", "log.json": True, "log.file": "/var/log/app.log",
    "feature.beta": True, "feature.search": False, "feature.export": True, "feature.audit": True,
    "limits.upload": 99, "limits.download": 999, "limits.requests": 5, "limits.jobs": 16,
}
MODULES = ["billing", "catalog", "checkout", "search", "exports", "mailer", "webhooks", "reports", "auth",
           "sessions", "uploads", "downloads", "scheduler", "audit", "metrics", "admin", "profiles", "tags",
           "comments", "ratings", "coupons", "shipping", "returns", "gateway", "invoices", "refunds", "payouts",
           "ledger", "taxes", "currency", "geo", "locale", "media", "thumbnails", "feeds", "sitemap", "robots",
           "health", "queue", "workers", "cron", "backups", "imports", "notifications", "sms", "push", "chat",
           "support"]

SOURCE = '''"""The raw configuration source: a dict filled from config.json at import (tests replace `values`)."""
import json
import pathlib

_PATH = pathlib.Path(__file__).resolve().parent.parent / "config.json"
values = json.loads(_PATH.read_text()) if _PATH.exists() else {}
'''

LEGACY = '''"""DEPRECATED untyped config access. Use app.settings (see MIGRATION.md)."""
from app import source


class _Cfg:
    def get(self, key, default=None):
        return source.values.get(key, default)

    def get_bool(self, key, default=False):
        value = source.values.get(key)
        if value is None:
            return default
        return str(value).lower() in ("1", "true", "yes")


cfg = _Cfg()
'''

SETTINGS = '''"""Typed settings: `settings.<section>.<key>`, with the defaults below when a key is unset."""
from app import source

DEFAULTS = %s
_SECTIONS = sorted({key.split(".")[0] for key in DEFAULTS})


def _coerce(key, value):
    default = DEFAULTS.get(key)
    if isinstance(default, bool):
        return str(value).lower() in ("1", "true", "yes")
    if isinstance(default, int):
        return int(value)
    return value


def lookup(key):
    """The value of key (e.g. "db.port"), or its default; KeyError for a key not in DEFAULTS."""
    if key not in DEFAULTS:
        raise KeyError(key)
    if key in source.values and source.values[key] is not None:
        return _coerce(key, source.values[key])
    return DEFAULTS[key]


def get_or(key, default):
    """The value of key, or `default` (not the DEFAULTS entry) when it is unset."""
    if key not in DEFAULTS:
        raise KeyError(key)
    if key in source.values and source.values[key] is not None:
        return _coerce(key, source.values[key])
    return default


class _Section:
    def __init__(self, name):
        self._name = name

    def __getattr__(self, attr):
        return lookup(f"{self._name}.{attr}")


class _Settings:
    def __getattr__(self, name):
        if name not in _SECTIONS:
            raise AttributeError(name)
        return _Section(name)


settings = _Settings()
'''

MIGRATION = """# Migrating off `app.legacy_cfg`

`app.legacy_cfg.cfg` is deprecated. Every module under `app/` must use `app.settings` instead, and
`app/legacy_cfg.py` is deleted once nothing imports it. Behaviour must not change: `python3 -m unittest`
must pass before and after (don't edit the tests).

Rules, for a key `"<section>.<name>"`:

1. `cfg.get(key, d)` where `d` equals the key's entry in `settings.DEFAULTS` becomes
   `settings.<section>.<name>` (`from app.settings import settings`).
2. `cfg.get(key)` (no default means `None`) or `cfg.get(key, d)` where `d` differs from the DEFAULTS entry
   becomes `get_or(key, d)` (`from app.settings import get_or`), which keeps the call site's own default.
3. `cfg.get_bool(key)` / `cfg.get_bool(key, d)`: the same two rules, with `False` as the implied default.
4. A key built at run time (`cfg.get(f"limits.{kind}", d)`) uses `get_or(f"limits.{kind}", d)`, or
   `lookup(f"limits.{kind}")` (`from app.settings import lookup`) when `d` always equals the DEFAULTS entry.
5. Conversions the old call sites needed (`int(...)`) may stay or go; settings values are already typed.
"""


def call(rng, key, kind):
    """Legacy expression for key; kind: same | other | none | bool."""
    d = DEFAULTS[key]
    if isinstance(d, bool):
        if kind == "other":
            return f'cfg.get_bool("{key}", {not d})'
        return f'cfg.get_bool("{key}")' if d is False else f'cfg.get_bool("{key}", True)'
    if kind == "none":
        return f'cfg.get("{key}")'
    if kind == "other":
        if isinstance(d, int):
            alt = d * 2 + 1
        elif d is None:
            alt = '"unset"'
            return f'cfg.get("{key}", {alt})'
        else:
            alt = d + "-alt"
        val = repr(alt)
    else:
        val = repr(d)
    expr = f'cfg.get("{key}", {val})'
    if isinstance(d, int) and kind != "none":
        expr = f"int({expr})"
    return expr


def module_source(rng, name, idx):
    keys = rng.sample(sorted(k for k in DEFAULTS if not k.startswith("limits.")), rng.randint(3, 4))
    head = [f'"""The {name} service."""', "from app.legacy_cfg import cfg", "", ""]
    body = ["def describe():", f'    """What the {name} service runs with."""']
    out = []
    kw_done = False
    for j, key in enumerate(keys):
        d = DEFAULTS[key]
        kind = rng.choice(["same", "same", "other", "none"]) if not isinstance(d, bool) else rng.choice(["same", "other"])
        if d is None and kind == "same":
            kind = "none"
        var = key.replace(".", "_")
        expr = call(rng, key, kind)
        if j == 0 and idx % 5 == 3:
            # Trap: the key comes from a module constant.
            const = var.upper() + "_KEY"
            head[2:2] = ["", f'{const} = "{key}"']
            expr = expr.replace(f'"{key}"', const)
        elif idx % 4 == 1 and not kw_done and "get_bool" not in expr and ", " in expr:
            kw_done = True
            # Trap: keyword arguments over several lines.
            k, v = expr[expr.index("cfg.get(") + 8:expr.rindex(")")].split(", ", 1)
            v = v.rstrip(")")
            inner = f"cfg.get(\n        key={k},\n        default={v},\n    )"
            expr = f"int({inner})" if expr.startswith("int(") else inner
        body.append(f"    {var} = {expr}")
        out.append(var)
    if idx % 6 == 2:
        # Trap: a nested legacy call as the default of another.
        body.append('    fallback_timeout = int(cfg.get("api.timeout", cfg.get("db.timeout", 30)))')
        out.append("fallback_timeout")
    sites = len(keys) + (2 if idx % 6 == 2 else 0)
    if idx % 3 == 0:
        kind_name = rng.choice(["upload", "download", "requests", "jobs"])
        default = DEFAULTS[f"limits.{kind_name}"] if idx % 2 == 0 else 1
        head += [f'def limit(kind="{kind_name}"):', f'    return int(cfg.get(f"limits.{{kind}}", {default}))', "", ""]
        out.append("limit()")
        sites += 1
    pairs = ", ".join(f'"{v.split("(")[0]}": {v}' for v in out)
    body.append(f"    return {{{pairs}}}")
    text = "\n".join(head + body) + "\n"
    if idx % 7 == 1:
        # Trap: an aliased import.
        text = text.replace("from app.legacy_cfg import cfg", "from app.legacy_cfg import cfg as conf").replace(
            "cfg.get", "conf.get")
    elif idx % 7 == 4:
        # Trap: the module imported, not the object.
        text = text.replace("from app.legacy_cfg import cfg", "from app import legacy_cfg").replace(
            "cfg.get", "legacy_cfg.cfg.get")
    return text, sites


def main():
    rng = random.Random(20261101)
    if OUT.exists():
        shutil.rmtree(OUT)
    (OUT / "app").mkdir(parents=True)
    (OUT / "tests").mkdir()
    (OUT / "app" / "__init__.py").write_text("")
    (OUT / "app" / "source.py").write_text(SOURCE)
    (OUT / "app" / "legacy_cfg.py").write_text(LEGACY)
    (OUT / "app" / "settings.py").write_text(SETTINGS % json.dumps(DEFAULTS, indent=4).replace("true", "True")
                                             .replace("false", "False").replace("null", "None"))
    (OUT / "MIGRATION.md").write_text(MIGRATION)
    (OUT / "AGENTS.md").write_text("Run tests with `python3 -m unittest` from the repo root. Standard library only.\n")
    sites = 0
    for i, name in enumerate(MODULES):
        src, n = module_source(rng, name, i)
        sites += n
        (OUT / "app" / f"{name}.py").write_text(src)
    sys.path.insert(0, str(OUT))
    import importlib
    source = importlib.import_module("app.source")
    expected = {}
    for name in MODULES:
        mod = importlib.import_module(f"app.{name}")
        for label, values in (("empty", {}), ("full", FULL)):
            source.values = dict(values)
            expected[f"{name}/{label}"] = mod.describe()
    test = ["import unittest", "", "from app import source", "from app import " + ", ".join(MODULES), "", "FULL = "
            + repr(FULL), "EXPECTED = " + repr(expected), "", "",
            "class DescribeTest(unittest.TestCase):", "    def tearDown(self):", "        source.values = {}", ""]
    for name in MODULES:
        test += [f"    def test_{name}(self):", "        for label, values in (('empty', {}), ('full', FULL)):",
                 "            source.values = dict(values)",
                 f"            self.assertEqual({name}.describe(), EXPECTED['{name}/' + label], label)", ""]
    test += ["", 'if __name__ == "__main__":', "    unittest.main()", ""]
    (OUT / "tests" / "__init__.py").write_text("")
    (OUT / "tests" / "test_describe.py").write_text("\n".join(test))
    r = subprocess.run([sys.executable, "-B", "-m", "unittest"], cwd=OUT, capture_output=True, text=True)
    assert r.returncode == 0, r.stderr[-2000:]
    HIDDEN.mkdir(parents=True, exist_ok=True)
    shutil.copy(OUT / "tests" / "test_describe.py", HIDDEN / "test_describe.py")
    for p in OUT.rglob("__pycache__"):
        shutil.rmtree(p)
    print("migrate ok, call sites:", sites)


if __name__ == "__main__":
    main()
