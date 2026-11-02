#!/usr/bin/env python3
"""Fixture `tickets`: 20 issues across a small package; hidden tests per issue (<data>/hidden/tickets)."""
import pathlib
import re
import shutil
import subprocess
import sys

ROOT = pathlib.Path(sys.argv[1]).resolve()  # the bench data dir
OUT = ROOT / "fixtures" / "tickets"
REF = ROOT / "ref" / "tickets"
HIDDEN = ROOT / "hidden" / "tickets"

ISSUES = """# Open issues

Issues build on each other where they say so. Money is integer cents everywhere. "Round half up" means
0.5 cent rounds up. Unless an issue says otherwise, existing behaviour stays as it is.

1. `pricing.apply_discount(cents, pct)` truncates. It must round half up to a whole cent:
   `apply_discount(999, 15)` is 849 (849.15 -> 849), `apply_discount(1001, 50)` is 501 (500.5 -> 501).
2. Add `pricing.bulk_price(unit_cents, qty)`: the total for qty units, 5% off the total when qty >= 10,
   10% off when qty >= 50, rounded half up. `bulk_price(199, 10)` is 1891.
3. `Cart.add(sku, qty)` called twice with the same sku creates two lines. It must add to the existing line;
   `Cart.lines()` keeps first-added order.
4. `Cart.total()` ignores shipping. Shipping is 499 when the subtotal is below 5000, free from 5000 up;
   an empty cart's total is 0.
5. `tax.tax_for(region, cents)` rejects "ca" or "Ca"; region codes must be case-insensitive.
6. Add region "NY" to `tax.RATES` at 8.875%. `tax_for` rounds half up to a whole cent (it truncates today):
   `tax_for("NY", 1000)` is 89.
7. `slugs.slugify("Héllo Wörld")` gives "hllo-wrld". Accented Latin letters must lose their accents
   instead: "hello-world".
8. `slugs.slugify("a  --  b")` gives "a----b". Runs of separators collapse to one dash, and the slug never
   starts or ends with a dash.
9. `dates.parse_date` reads "01/11/2026" as January 11. Slash dates are day/month/year (1 November 2026).
   ISO dates ("2026-11-01") keep working.
10. `report.sales_report(orders)` must end with a line `TOTAL <amount>`, the sum of all order totals in
    dollars with thousands separators and 2 decimals, e.g. `TOTAL 12,345.67`.
11. `csvio.read_orders(path)` breaks on quoted fields that contain commas (`"Smith, Jane"`). Use proper CSV
    parsing; the header row stays required.
12. `python3 -m shopkit --version` must print `shopkit <version>` from `shopkit.__version__` and exit 0.
13. Add coupons: `shopkit/coupons.py` with `COUPONS = {"SAVE10": 10, "HALF": 50}` (percent off), and
    `Cart.apply_coupon(code)`. An unknown code raises KeyError; a second coupon replaces the first. With a
    coupon, `Cart.total()` is the discounted subtotal (`apply_discount`, issue 1) plus shipping, and the
    shipping threshold of issue 4 applies to the discounted subtotal. `subtotal()` stays undiscounted.
14. `Cart(prices, region=None)`: with a region, `total()` also adds `tax_for(region, discounted subtotal)`
    (issues 5 and 6). Shipping is not taxed.
15. `slugify(text, max_len=40)`: the slug is at most max_len characters. When it must be cut, cut at the
    last dash that keeps it within max_len so no word is split; if the first word alone is longer than
    max_len, cut that word at max_len. The slug never ends with a dash (issue 8).
16. `parse_date` also accepts "1 Nov 2026" and "01-Nov-2026" (English month abbreviations, any case).
17. `sales_report(orders)`: when orders carry a "date" (a string `parse_date` accepts), the order lines
    are sorted by date, then by id; orders without a date come after them in their input order. The
    TOTAL line (issue 10) stays last.
18. `read_orders` also accepts the header `id,customer,total,date` (each order then gets its "date"
    string). A total with a decimal point is in dollars ("12.34" is 1234, "0.5" is 50), converted
    exactly; a total without one is cents, as today.
19. `sales_report(orders, currency=None)`: with currency "USD", "EUR" or "GBP" the TOTAL amount gets the
    prefix "$", "€" or "£" (`TOTAL €12,345.67`); other codes raise ValueError. The CLI takes
    `--currency CODE` and passes it on: `python3 -m shopkit orders.csv --currency EUR`.
20. `bulk_price(unit_cents, qty, coupon=0)`: an optional coupon percent applied after the bulk discount,
    rounding half up only once, at the end (`bulk_price(199, 10, coupon=10)` is 1701).
"""

BUGGY = {
    "shopkit/__init__.py": '__version__ = "1.4.0"\n',
    "shopkit/pricing.py": '''"""Prices in integer cents."""


def apply_discount(cents, pct):
    """Price after a pct% discount."""
    return int(cents * (100 - pct) / 100)
''',
    "shopkit/cart.py": '''"""Shopping cart."""


class Cart:
    def __init__(self, prices):
        self.prices = prices  # sku -> unit cents
        self._lines = []  # [sku, qty]

    def add(self, sku, qty=1):
        if sku not in self.prices:
            raise KeyError(sku)
        self._lines.append([sku, qty])

    def lines(self):
        return [tuple(line) for line in self._lines]

    def subtotal(self):
        return sum(self.prices[sku] * qty for sku, qty in self._lines)

    def total(self):
        return self.subtotal()
''',
    "shopkit/tax.py": '''"""Sales tax."""

RATES = {"CA": 7.25, "TX": 6.25, "OR": 0.0}


def tax_for(region, cents):
    rate = RATES[region]
    return int(cents * rate / 100)
''',
    "shopkit/slugs.py": '''"""URL slugs."""
import re


def slugify(text):
    text = text.lower()
    text = re.sub(r"[^a-z0-9\\s-]", "", text)
    return re.sub(r"\\s", "-", text.strip())
''',
    "shopkit/dates.py": '''"""Order date parsing."""
import datetime as dt


def parse_date(text):
    text = text.strip()
    if "/" in text:
        return dt.datetime.strptime(text, "%m/%d/%Y").date()
    return dt.date.fromisoformat(text)
''',
    "shopkit/report.py": '''"""Plain-text sales report."""


def sales_report(orders):
    """orders: list of dicts with "id" and "total" (cents)."""
    lines = [f"{o['id']}: {o['total'] / 100:.2f}" for o in orders]
    return "\\n".join(lines)
''',
    "shopkit/csvio.py": '''"""Order CSV files: header id,customer,total."""


def read_orders(path):
    with open(path) as fh:
        rows = fh.read().splitlines()
    header = rows[0].split(",")
    if header != ["id", "customer", "total"]:
        raise ValueError(f"bad header {header}")
    out = []
    for row in rows[1:]:
        if not row.strip():
            continue
        oid, customer, total = row.split(",")
        out.append({"id": oid, "customer": customer, "total": int(total)})
    return out
''',
    "shopkit/__main__.py": '''import argparse

from . import report


def main():
    parser = argparse.ArgumentParser(prog="shopkit")
    parser.add_argument("orders", nargs="?")
    args = parser.parse_args()
    if args.orders:
        from .csvio import read_orders
        print(report.sales_report(read_orders(args.orders)))


main()
''',
    "tests/__init__.py": "",
    "tests/test_basic.py": '''import unittest

from shopkit.cart import Cart
from shopkit.pricing import apply_discount


class BasicTest(unittest.TestCase):
    def test_discount_whole(self):
        self.assertEqual(apply_discount(1000, 10), 900)

    def test_cart_subtotal(self):
        c = Cart({"a": 100, "b": 250})
        c.add("a", 2)
        c.add("b")
        self.assertEqual(c.subtotal(), 450)


if __name__ == "__main__":
    unittest.main()
''',
    "AGENTS.md": "Run tests with `python3 -m unittest` from the repo root. Standard library only.\n",
}
BUGGY["ISSUES.md"] = ISSUES

REF_FILES = {
    "shopkit/pricing.py": '''"""Prices in integer cents."""
from decimal import ROUND_HALF_UP, Decimal


def _round(x):
    return int(Decimal(x).quantize(Decimal(1), rounding=ROUND_HALF_UP))


def apply_discount(cents, pct):
    """Price after a pct% discount."""
    return _round(Decimal(cents) * (100 - Decimal(str(pct))) / 100)


def bulk_price(unit_cents, qty):
    total = Decimal(unit_cents) * qty
    if qty >= 50:
        total = total * Decimal("0.90")
    elif qty >= 10:
        total = total * Decimal("0.95")
    return _round(total)
''',
    "shopkit/cart.py": '''"""Shopping cart."""


class Cart:
    def __init__(self, prices):
        self.prices = prices
        self._lines = []

    def add(self, sku, qty=1):
        if sku not in self.prices:
            raise KeyError(sku)
        for line in self._lines:
            if line[0] == sku:
                line[1] += qty
                return
        self._lines.append([sku, qty])

    def lines(self):
        return [tuple(line) for line in self._lines]

    def subtotal(self):
        return sum(self.prices[sku] * qty for sku, qty in self._lines)

    def total(self):
        sub = self.subtotal()
        if not self._lines:
            return 0
        return sub + (0 if sub >= 5000 else 499)
''',
    "shopkit/tax.py": '''"""Sales tax."""
from decimal import ROUND_HALF_UP, Decimal

RATES = {"CA": 7.25, "TX": 6.25, "OR": 0.0, "NY": 8.875}


def tax_for(region, cents):
    rate = RATES[region.upper()]
    return int((Decimal(cents) * Decimal(str(rate)) / 100).quantize(Decimal(1), rounding=ROUND_HALF_UP))
''',
    "shopkit/slugs.py": '''"""URL slugs."""
import re
import unicodedata


def slugify(text):
    text = unicodedata.normalize("NFKD", text).encode("ascii", "ignore").decode().lower()
    text = re.sub(r"[^a-z0-9\\s-]", "", text)
    return re.sub(r"[\\s-]+", "-", text).strip("-")
''',
    "shopkit/dates.py": '''"""Order date parsing."""
import datetime as dt


def parse_date(text):
    text = text.strip()
    if "/" in text:
        return dt.datetime.strptime(text, "%d/%m/%Y").date()
    return dt.date.fromisoformat(text)
''',
    "shopkit/report.py": '''"""Plain-text sales report."""


def sales_report(orders):
    lines = [f"{o['id']}: {o['total'] / 100:.2f}" for o in orders]
    total = sum(o["total"] for o in orders)
    lines.append(f"TOTAL {total // 100:,}.{total % 100:02d}")
    return "\\n".join(lines)
''',
    "shopkit/csvio.py": '''"""Order CSV files: header id,customer,total."""
import csv


def read_orders(path):
    with open(path, newline="") as fh:
        rows = [r for r in csv.reader(fh)]
    header = rows[0]
    if header != ["id", "customer", "total"]:
        raise ValueError(f"bad header {header}")
    return [{"id": r[0], "customer": r[1], "total": int(r[2])} for r in rows[1:] if r]
''',
    "shopkit/__main__.py": '''import argparse

from . import __version__, report


def main():
    parser = argparse.ArgumentParser(prog="shopkit")
    parser.add_argument("--version", action="version", version=f"shopkit {__version__}")
    parser.add_argument("orders", nargs="?")
    args = parser.parse_args()
    if args.orders:
        from .csvio import read_orders
        print(report.sales_report(read_orders(args.orders)))


main()
''',
}

HIDDEN_TESTS = '''import datetime as dt
import os
import subprocess
import sys
import tempfile
import unittest

from shopkit import cart, dates, pricing, report, slugs, tax
from shopkit import csvio


class Issue01(unittest.TestCase):
    def test(self):
        self.assertEqual([pricing.apply_discount(999, 15), pricing.apply_discount(1001, 50),
                          pricing.apply_discount(1000, 10), pricing.apply_discount(1, 50)], [849, 501, 900, 1])


class Issue02(unittest.TestCase):
    def test(self):
        self.assertEqual([pricing.bulk_price(199, 10), pricing.bulk_price(199, 9), pricing.bulk_price(100, 50),
                          pricing.bulk_price(10, 49), pricing.bulk_price(7, 50)], [1891, 1791, 4500, 466, 315])


class Issue03(unittest.TestCase):
    def test(self):
        c = cart.Cart({"a": 100, "b": 5})
        c.add("b", 1)
        c.add("a", 2)
        c.add("b", 3)
        self.assertEqual(c.lines(), [("b", 4), ("a", 2)])
        self.assertEqual(c.subtotal(), 220)


class Issue04(unittest.TestCase):
    def test(self):
        c = cart.Cart({"a": 4999, "b": 1})
        self.assertEqual(c.total(), 0)
        c.add("a")
        self.assertEqual(c.total(), 4999 + 499)
        c.add("b")
        self.assertEqual(c.total(), 5000)


class Issue05(unittest.TestCase):
    def test(self):
        self.assertEqual([tax.tax_for("ca", 10000), tax.tax_for("Ca", 10000), tax.tax_for("tx", 400)], [725, 725, 25])


class Issue06(unittest.TestCase):
    def test(self):
        self.assertEqual(tax.RATES["NY"], 8.875)
        self.assertEqual([tax.tax_for("NY", 1000), tax.tax_for("ny", 200), tax.tax_for("CA", 1000)], [89, 18, 73])


class Issue07(unittest.TestCase):
    def test(self):
        self.assertEqual([slugs.slugify("Héllo Wörld"), slugs.slugify("Crème Brûlée"), slugs.slugify("Ça va")],
                         ["hello-world", "creme-brulee", "ca-va"])


class Issue08(unittest.TestCase):
    def test(self):
        self.assertEqual([slugs.slugify("a  --  b"), slugs.slugify(" -x- "), slugs.slugify("one two")],
                         ["a-b", "x", "one-two"])


class Issue09(unittest.TestCase):
    def test(self):
        self.assertEqual([dates.parse_date("01/11/2026"), dates.parse_date("25/12/2026"), dates.parse_date("2026-11-01")],
                         [dt.date(2026, 11, 1), dt.date(2026, 12, 25), dt.date(2026, 11, 1)])


class Issue10(unittest.TestCase):
    def test(self):
        out = report.sales_report([{"id": "o1", "total": 1234500}, {"id": "o2", "total": 67}])
        self.assertEqual(out.splitlines()[-1], "TOTAL 12,345.67")
        self.assertEqual(out.splitlines()[0], "o1: 12345.00")


class Issue11(unittest.TestCase):
    def test(self):
        with tempfile.NamedTemporaryFile("w", suffix=".csv", delete=False) as fh:
            fh.write('id,customer,total\\no1,"Smith, Jane",1200\\no2,Bob,5\\n')
        try:
            self.assertEqual(csvio.read_orders(fh.name), [{"id": "o1", "customer": "Smith, Jane", "total": 1200},
                                                          {"id": "o2", "customer": "Bob", "total": 5}])
        finally:
            os.unlink(fh.name)


class Issue12(unittest.TestCase):
    def test(self):
        r = subprocess.run([sys.executable, "-m", "shopkit", "--version"], capture_output=True, text=True)
        self.assertEqual((r.returncode, r.stdout.strip()), (0, "shopkit 1.4.0"))


if __name__ == "__main__":
    unittest.main()
'''

REF_FILES.update({
    "shopkit/pricing.py": '''"""Prices in integer cents."""
from decimal import ROUND_HALF_UP, Decimal


def _round(x):
    return int(Decimal(x).quantize(Decimal(1), rounding=ROUND_HALF_UP))


def apply_discount(cents, pct):
    return _round(Decimal(cents) * (100 - Decimal(str(pct))) / 100)


def bulk_price(unit_cents, qty, coupon=0):
    total = Decimal(unit_cents) * qty
    if qty >= 50:
        total = total * Decimal("0.90")
    elif qty >= 10:
        total = total * Decimal("0.95")
    total = total * (100 - Decimal(str(coupon))) / 100
    return _round(total)
''',
    "shopkit/coupons.py": 'COUPONS = {"SAVE10": 10, "HALF": 50}\n',
    "shopkit/cart.py": '''"""Shopping cart."""
from .coupons import COUPONS
from .pricing import apply_discount
from .tax import tax_for


class Cart:
    def __init__(self, prices, region=None):
        self.prices = prices
        self.region = region
        self.coupon = None
        self._lines = []

    def add(self, sku, qty=1):
        if sku not in self.prices:
            raise KeyError(sku)
        for line in self._lines:
            if line[0] == sku:
                line[1] += qty
                return
        self._lines.append([sku, qty])

    def apply_coupon(self, code):
        if code not in COUPONS:
            raise KeyError(code)
        self.coupon = code

    def lines(self):
        return [tuple(line) for line in self._lines]

    def subtotal(self):
        return sum(self.prices[sku] * qty for sku, qty in self._lines)

    def total(self):
        if not self._lines:
            return 0
        sub = self.subtotal()
        if self.coupon:
            sub = apply_discount(sub, COUPONS[self.coupon])
        tax = tax_for(self.region, sub) if self.region else 0
        return sub + tax + (0 if sub >= 5000 else 499)
''',
    "shopkit/slugs.py": '''"""URL slugs."""
import re
import unicodedata


def slugify(text, max_len=40):
    text = unicodedata.normalize("NFKD", text).encode("ascii", "ignore").decode().lower()
    text = re.sub(r"[^a-z0-9\\s-]", "", text)
    slug = re.sub(r"[\\s-]+", "-", text).strip("-")
    if len(slug) <= max_len:
        return slug
    cut = slug[:max_len + 1]
    if cut.endswith("-"):
        return cut[:-1]
    head = slug[:max_len]
    if "-" in head:
        return head[:head.rindex("-")]
    return head
''',
    "shopkit/dates.py": '''"""Order date parsing."""
import datetime as dt

MONTHS = ["jan", "feb", "mar", "apr", "may", "jun", "jul", "aug", "sep", "oct", "nov", "dec"]


def parse_date(text):
    text = text.strip()
    if "/" in text:
        return dt.datetime.strptime(text, "%d/%m/%Y").date()
    parts = text.replace("-", " ").split()
    if len(parts) == 3 and parts[1].lower() in MONTHS:
        return dt.date(int(parts[2]), MONTHS.index(parts[1].lower()) + 1, int(parts[0]))
    return dt.date.fromisoformat(text)
''',
    "shopkit/report.py": '''"""Plain-text sales report."""
from .dates import parse_date

SYMBOLS = {"USD": "$", "EUR": "€", "GBP": "£"}


def sales_report(orders, currency=None):
    if currency is not None and currency not in SYMBOLS:
        raise ValueError(currency)
    dated = sorted((o for o in orders if o.get("date")), key=lambda o: (parse_date(o["date"]), o["id"]))
    rest = [o for o in orders if not o.get("date")]
    lines = [f"{o['id']}: {o['total'] / 100:.2f}" for o in dated + rest]
    total = sum(o["total"] for o in orders)
    lines.append(f"TOTAL {SYMBOLS.get(currency, '')}{total // 100:,}.{total % 100:02d}")
    return "\\n".join(lines)
''',
    "shopkit/csvio.py": '''"""Order CSV files: header id,customer,total[,date]."""
import csv
from decimal import Decimal


def _cents(text):
    if "." in text:
        return int(Decimal(text) * 100)
    return int(text)


def read_orders(path):
    with open(path, newline="") as fh:
        rows = list(csv.reader(fh))
    header = rows[0]
    if header not in (["id", "customer", "total"], ["id", "customer", "total", "date"]):
        raise ValueError(f"bad header {header}")
    out = []
    for r in rows[1:]:
        if not r:
            continue
        order = {"id": r[0], "customer": r[1], "total": _cents(r[2])}
        if len(header) == 4:
            order["date"] = r[3]
        out.append(order)
    return out
''',
    "shopkit/__main__.py": '''import argparse

from . import __version__, report


def main():
    parser = argparse.ArgumentParser(prog="shopkit")
    parser.add_argument("--version", action="version", version=f"shopkit {__version__}")
    parser.add_argument("--currency")
    parser.add_argument("orders", nargs="?")
    args = parser.parse_args()
    if args.orders:
        from .csvio import read_orders
        print(report.sales_report(read_orders(args.orders), currency=args.currency))


main()
''',
})

HIDDEN_TESTS = HIDDEN_TESTS.replace('\nif __name__ == "__main__":', '''
def _cart(prices, **kw):
    return cart.Cart(prices, **kw)


class Issue13(unittest.TestCase):
    def test(self):
        from shopkit import coupons
        self.assertEqual(coupons.COUPONS, {"SAVE10": 10, "HALF": 50})
        c = _cart({"a": 5500, "b": 999})
        c.add("a")
        self.assertEqual(c.total(), 5500)
        c.apply_coupon("SAVE10")
        self.assertEqual((c.subtotal(), c.total()), (5500, 4950 + 499))
        c.apply_coupon("HALF")
        self.assertEqual(c.total(), 2750 + 499)
        with self.assertRaises(KeyError):
            c.apply_coupon("NOPE")
        d = _cart({"b": 999})
        d.add("b", 1)
        d.apply_coupon("HALF")
        self.assertEqual(d.total(), 500 + 499)
        e = _cart({"b": 1})
        e.apply_coupon("HALF")
        self.assertEqual(e.total(), 0)


class Issue14(unittest.TestCase):
    def test(self):
        c = _cart({"a": 1000}, region="ny")
        c.add("a")
        self.assertEqual(c.total(), 1000 + 89 + 499)
        c.apply_coupon("SAVE10")
        self.assertEqual(c.total(), 900 + 80 + 499)
        d = _cart({"a": 6000}, region="CA")
        d.add("a")
        self.assertEqual(d.total(), 6000 + 435)
        self.assertEqual(_cart({"a": 1}).total(), 0)


class Issue15(unittest.TestCase):
    def test(self):
        s = slugs.slugify
        self.assertEqual([s("one two three", max_len=9), s("one two three", max_len=7), s("one two three", max_len=8),
                          s("abcdefghij", max_len=4), s("a b", max_len=40), s("Héllo  Wörld again", max_len=11)],
                         ["one-two", "one-two", "one-two", "abcd", "a-b", "hello-world"])
        long = " ".join(["word"] * 20)
        self.assertEqual(s(long), "-".join(["word"] * 8))


class Issue16(unittest.TestCase):
    def test(self):
        p = dates.parse_date
        self.assertEqual([p("1 Nov 2026"), p("01-Nov-2026"), p("15 DEC 2025"), p("3-feb-2027"), p("02/01/2026")],
                         [dt.date(2026, 11, 1), dt.date(2026, 11, 1), dt.date(2025, 12, 15), dt.date(2027, 2, 3),
                          dt.date(2026, 1, 2)])


class Issue17(unittest.TestCase):
    def test(self):
        orders = [{"id": "z", "total": 1}, {"id": "b", "total": 2, "date": "02/11/2026"},
                  {"id": "a", "total": 3, "date": "2026-11-02"}, {"id": "c", "total": 4, "date": "1 Nov 2026"},
                  {"id": "y", "total": 5}]
        out = report.sales_report(orders).splitlines()
        self.assertEqual(out, ["c: 0.04", "a: 0.03", "b: 0.02", "z: 0.01", "y: 0.05", "TOTAL 0.15"])


class Issue18(unittest.TestCase):
    def test(self):
        with tempfile.NamedTemporaryFile("w", suffix=".csv", delete=False) as fh:
            fh.write('id,customer,total,date\\no1,"Doe, J",12.34,2026-11-01\\no2,Bob,0.5,1 Nov 2026\\no3,Al,7,\\n'
                     'o4,Cy,0.29,02/11/2026\\n')
        try:
            got = csvio.read_orders(fh.name)
        finally:
            os.unlink(fh.name)
        self.assertEqual(got, [{"id": "o1", "customer": "Doe, J", "total": 1234, "date": "2026-11-01"},
                               {"id": "o2", "customer": "Bob", "total": 50, "date": "1 Nov 2026"},
                               {"id": "o3", "customer": "Al", "total": 7, "date": ""},
                               {"id": "o4", "customer": "Cy", "total": 29, "date": "02/11/2026"}])


class Issue19(unittest.TestCase):
    def test(self):
        o = [{"id": "a", "total": 1234567}]
        self.assertEqual([report.sales_report(o, currency=c).splitlines()[-1] for c in ("EUR", "GBP", "USD", None)],
                         ["TOTAL €12,345.67", "TOTAL £12,345.67", "TOTAL $12,345.67", "TOTAL 12,345.67"])
        with self.assertRaises(ValueError):
            report.sales_report(o, currency="JPY")
        with tempfile.NamedTemporaryFile("w", suffix=".csv", delete=False) as fh:
            fh.write("id,customer,total\\no1,A,1500\\n")
        try:
            r = subprocess.run([sys.executable, "-m", "shopkit", fh.name, "--currency", "EUR"], capture_output=True,
                               text=True, env={**os.environ, "PYTHONIOENCODING": "utf-8"})
        finally:
            os.unlink(fh.name)
        self.assertEqual((r.returncode, r.stdout.splitlines()), (0, ["o1: 15.00", "TOTAL €15.00"]))


class Issue20(unittest.TestCase):
    def test(self):
        self.assertEqual([pricing.bulk_price(199, 10, coupon=10), pricing.bulk_price(199, 10),
                          pricing.bulk_price(100, 50, coupon=50), pricing.bulk_price(3, 1, coupon=50)],
                         [1701, 1891, 2250, 2])


if __name__ == "__main__":''')
assert "Issue20" in HIDDEN_TESTS


def write(base, files):
    for rel, text in files.items():
        p = base / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)


def hidden_failures(base):
    t = base / "hidden_tickets_test.py"
    t.write_text(HIDDEN_TESTS)
    r = subprocess.run([sys.executable, "-B", "-m", "unittest", "-v", "hidden_tickets_test"], cwd=base,
                       capture_output=True, text=True)
    t.unlink()
    return sorted({m.group() for ln in r.stderr.splitlines() if ln.endswith(("FAIL", "ERROR"))
                   for m in [re.search(r"Issue\d\d", ln)] if m})


def main():
    for d in (OUT, REF):
        if d.exists():
            shutil.rmtree(d)
    write(OUT, BUGGY)
    write(REF, {**BUGGY, **REF_FILES})
    assert hidden_failures(REF) == [], hidden_failures(REF)
    fails = hidden_failures(OUT)
    assert fails == [f"Issue{i:02d}" for i in range(1, 21)], fails
    HIDDEN.mkdir(parents=True, exist_ok=True)
    (HIDDEN / "hidden_tickets_test.py").write_text(HIDDEN_TESTS)
    r = subprocess.run([sys.executable, "-B", "-m", "unittest"], cwd=OUT, capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    print("tickets ok")


if __name__ == "__main__":
    main()
