#!/usr/bin/env python3
"""Fixture `relay`: 17 legacy_hash call sites across 10 modules, for a parent -> child message task."""
import json
import pathlib
import shutil
import subprocess
import sys

ROOT = pathlib.Path(sys.argv[1]).resolve()  # the bench data dir
OUT = ROOT / "fixtures" / "relay"

HASHING = '''"""Hash helpers. legacy_hash is deprecated: new code uses stable_hash."""
import hashlib
import zlib


def legacy_hash(value):
    return format(zlib.crc32(str(value).encode()), "08x")


def stable_hash(value):
    return hashlib.sha256(str(value).encode()).hexdigest()[:12]
'''

# module name -> list of (function name, expression body using H(...))
MODULES = {
    "users": [("user_key", "H(name.lower())"), ("email_key", "H(email.strip())")],
    "orders": [("order_key", "H(f\"{customer}:{number}\")")],
    "invoices": [("invoice_key", "H(number)"), ("line_key", "H((number, line))")],
    "sessions": [("session_key", "H(token)")],
    "carts": [("cart_key", "H(customer)"), ("item_key", "H(sku)"), ("bundle_key", "H(tuple(sorted(skus)))")],
    "audit": [("event_key", "H(event)")],
    "files": [("path_key", "H(path.rstrip('/'))"), ("blob_key", "H(len(data))")],
    "tags": [("tag_key", "H(tag)")],
    "shipments": [("tracking_key", "H(tracking.upper())"), ("parcel_key", "H(f\"{tracking}#{n}\")")],
    "coupons": [("coupon_key", "H(code)"), ("campaign_key", "H(campaign)")],
}
ARGS = {
    "user_key": "name", "email_key": "email", "order_key": "customer, number", "invoice_key": "number",
    "line_key": "number, line", "session_key": "token", "cart_key": "customer", "item_key": "sku",
    "bundle_key": "skus", "event_key": "event", "path_key": "path", "blob_key": "data", "tag_key": "tag",
    "tracking_key": "tracking", "parcel_key": "tracking, n", "coupon_key": "code", "campaign_key": "campaign",
}
SAMPLE = {
    "user_key": ("Ada",), "email_key": (" ada@example.com ",), "order_key": ("c1", 7), "invoice_key": (42,),
    "line_key": (42, 3), "session_key": ("tok",), "cart_key": ("c9",), "item_key": ("SKU-1",),
    "bundle_key": (["b", "a"],), "event_key": ("login",), "path_key": ("/srv/x/",), "blob_key": (b"abc",),
    "tag_key": ("red",), "tracking_key": ("zx1",), "parcel_key": ("ZX1", 2), "coupon_key": ("SAVE",),
    "campaign_key": ("fall",),
}


def module_source(name, funcs, fn):
    lines = [f'"""{name.capitalize()} identifiers."""', "from ids import hashing", ""]
    for func, body in funcs:
        lines += ["", f"def {func}({ARGS[func]}):", f"    return hashing.{fn}({body[2:-1]})", ""]
    return "\n".join(lines).rstrip() + "\n"


def main():
    if OUT.exists():
        shutil.rmtree(OUT)
    pkg = OUT / "ids"
    (OUT / "tests").mkdir(parents=True)
    pkg.mkdir()
    (pkg / "__init__.py").write_text("")
    (pkg / "hashing.py").write_text(HASHING)
    sys.path.insert(0, str(OUT))
    import importlib
    hashing = importlib.import_module("ids.hashing")
    expected = {}
    for name, funcs in MODULES.items():
        (pkg / f"{name}.py").write_text(module_source(name, funcs, "stable_hash"))
        mod = importlib.import_module(f"ids.{name}")
        for func, _ in funcs:
            expected[f"{name}.{func}"] = getattr(mod, func)(*SAMPLE[func])
        (pkg / f"{name}.py").write_text(module_source(name, funcs, "legacy_hash"))
    assert hashing.stable_hash("x") != hashing.legacy_hash("x")
    tests = ["import unittest", "", "from ids import " + ", ".join(MODULES), "", "",
             "class StableIdsTest(unittest.TestCase):", "    def test_ids_use_stable_hash(self):",
             "        cases = ["]
    for key, val in expected.items():
        mod, func = key.split(".")
        tests.append(f"            ({mod}.{func}(*{SAMPLE[func]!r}), {val!r}),")
    tests += ["        ]", "        for got, want in cases:", "            self.assertEqual(got, want)", "", "",
              'if __name__ == "__main__":', "    unittest.main()", ""]
    (OUT / "tests" / "__init__.py").write_text("")
    (OUT / "tests" / "test_ids.py").write_text("\n".join(tests))
    calls = sum(p.read_text().count("legacy_hash(") for p in pkg.glob("*.py") if p.name != "hashing.py")
    assert calls == 17, calls
    r = subprocess.run([sys.executable, "-m", "unittest"], cwd=OUT, capture_output=True, text=True)
    assert r.returncode != 0
    print("relay ok, call sites:", calls, json.dumps(expected)[:80])


if __name__ == "__main__":
    main()
