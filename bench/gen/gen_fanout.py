#!/usr/bin/env python3
"""Fixture `fanout`: four independent packages, each with seeded bugs and failing tests.

Writes <data>/fixtures/fanout (bugged), <data>/ref/fanout (fixed) and <data>/expected/fanout.json (selfcheck
lines of the fixed code). Usage: gen_fanout.py <data-dir>.
"""
import json
import pathlib
import shutil
import subprocess
import sys

ROOT = pathlib.Path(sys.argv[1]).resolve()  # the bench data dir
OUT = ROOT / "fixtures" / "fanout"
REF = ROOT / "ref" / "fanout"

SELFCHECK = '''import hashlib
import json

from . import cases


def main():
    blob = json.dumps(cases.run(), sort_keys=True, default=str)
    print(f"{__package__} OK {hashlib.sha256(blob.encode()).hexdigest()[:10]}")


if __name__ == "__main__":
    main()
'''

# One more function per package, specified only by its docstring: its bug fails no visible test, only the
# self-check (the prompt says the docstrings are the spec).
EXTRA = {
    "intervals": ('''

def gaps(intervals):
    """The integers strictly between consecutive normalized intervals, as normalized intervals."""
    norm = normalize(intervals)
    return [(a_end + 1, b_start - 1) for (_, a_end), (b_start, _) in zip(norm, norm[1:])]
''', "from .core import gaps", "[gaps(d) for d in DATA]",
        ("(a_end + 1, b_start - 1)", "(a_end, b_start)")),
    "textstats": ('''

def longest_sentence(text):
    """The sentence (as sentences() gives it) with the most words; the first one on ties."""
    best = None
    for s in sentences(text):
        if best is None or len(words(s)) > len(words(best)):
            best = s
    return best
''', "from .core import longest_sentence", '[longest_sentence(t) for t in TEXTS + ["One two. Three four. Five."]]',
        ("len(words(s)) > len(words(best))", "len(words(s)) >= len(words(best))")),
    "inventory": ('''

def average_cost(item):
    """Weighted average unit cost (cents) of the units on hand, rounded half up; 0 when nothing is on hand."""
    qty = item.on_hand()
    if not qty:
        return 0
    return (2 * item.value() + qty) // (2 * qty)
''', "from .core import Item, average_cost", "[average_cost(i) for i in _items()]",
        ("    return (2 * item.value() + qty) // (2 * qty)",
         "    return round(sum(lot.unit_cost for lot in item.lots) / len(item.lots))")),
    "isoweek": ('''

def weeks_in_year(year):
    """Number of ISO weeks in ISO year `year`: 53 when Jan 1 is a Thursday, or a Wednesday in a leap year; else 52."""
    jan1 = dt.date(year, 1, 1).weekday()
    leap = year % 4 == 0 and (year % 100 != 0 or year % 400 == 0)
    return 53 if jan1 == 3 or (jan1 == 2 and leap) else 52
''', "from .core import weeks_in_year", "[weeks_in_year(y) for y in (2015, 2020, 2026, 2027, 2032, 2100, 2000)]",
        ("    return 53 if jan1 == 3 or (jan1 == 2 and leap) else 52", "    return 53 if jan1 == 3 else 52")),
}


PKGS = {}

PKGS["intervals"] = {
    "core.py": '''"""Closed integer intervals [start, end], start <= end."""


def normalize(intervals):
    """Sort and merge intervals; touching intervals ([1, 3] and [4, 6]) merge too."""
    out = []
    for start, end in sorted(intervals):
        if start > end:
            raise ValueError(f"bad interval {start, end}")
        if out and start <= out[-1][1] + 1:
            out[-1][1] = max(out[-1][1], end)
        else:
            out.append([start, end])
    return [tuple(iv) for iv in out]


def total_length(intervals):
    """Number of integers covered."""
    return sum(end - start + 1 for start, end in normalize(intervals))


def subtract(intervals, holes):
    """The integers in `intervals` but not in `holes`, normalized."""
    result = []
    holes = normalize(holes)
    for start, end in normalize(intervals):
        cur = start
        for hs, he in holes:
            if he < cur or hs > end:
                continue
            if hs > cur:
                result.append((cur, hs - 1))
            cur = max(cur, he + 1)
        if cur <= end:
            result.append((cur, end))
    return normalize(result)


def intersect(a, b):
    """The integers in both."""
    a, b = normalize(a), normalize(b)
    i = j = 0
    out = []
    while i < len(a) and j < len(b):
        lo = max(a[i][0], b[j][0])
        hi = min(a[i][1], b[j][1])
        if lo <= hi:
            out.append((lo, hi))
        if a[i][1] < b[j][1]:
            i += 1
        else:
            j += 1
    return normalize(out)
''',
    "cases.py": '''from .core import intersect, normalize, subtract, total_length

DATA = [
    [(5, 9), (1, 3), (4, 4), (20, 25), (12, 12)],
    [(0, 100)],
    [(7, 7), (8, 8), (10, 10)],
    [(3, 30), (5, 6), (31, 40), (50, 51)],
]
HOLES = [[(2, 5), (21, 21)], [(0, 0), (100, 100), (50, 60)], [(8, 9)], [(1, 4), (40, 52)]]


def run():
    out = []
    for d, h in zip(DATA, HOLES):
        out.append([normalize(d), total_length(d), subtract(d, h), intersect(d, h)])
    return out
''',
    "tests/test_core.py": '''import unittest

from intervals.core import intersect, normalize, subtract, total_length


class CoreTest(unittest.TestCase):
    def test_normalize_merges_touching(self):
        self.assertEqual(normalize([(4, 6), (1, 3), (8, 9)]), [(1, 6), (8, 9)])

    def test_normalize_nested(self):
        self.assertEqual(normalize([(1, 10), (2, 3)]), [(1, 10)])

    def test_total_length(self):
        self.assertEqual(total_length([(1, 3), (2, 5), (10, 10)]), 6)

    def test_subtract_middle(self):
        self.assertEqual(subtract([(1, 10)], [(4, 5)]), [(1, 3), (6, 10)])

    def test_subtract_edges(self):
        self.assertEqual(subtract([(1, 10)], [(1, 2), (10, 12)]), [(3, 9)])

    def test_intersect(self):
        self.assertEqual(intersect([(1, 5), (8, 12)], [(4, 9), (12, 20)]), [(4, 5), (8, 9), (12, 12)])


if __name__ == "__main__":
    unittest.main()
''',
    "bugs": [
        ("if out and start <= out[-1][1] + 1:", "if out and start <= out[-1][1]:"),
        ("    return sum(end - start + 1 for start, end in normalize(intervals))",
         "    return sum(end - start for start, end in normalize(intervals))"),
        ("            cur = max(cur, he + 1)", "            cur = max(cur, he)"),
        ("        if a[i][1] < b[j][1]:", "        if a[i][1] <= b[j][0]:"),
    ],
}

PKGS["textstats"] = {
    "core.py": '''"""Word and sentence statistics for English text."""
import re

WORD = re.compile(r"[A-Za-z]+(?:'[A-Za-z]+)?")
ABBREVIATIONS = {"mr", "mrs", "dr", "e.g", "i.e", "etc"}


def words(text):
    return [w.lower() for w in WORD.findall(text)]


def top_words(text, k):
    """The k most frequent words as (word, count), ties broken alphabetically."""
    counts = {}
    for w in words(text):
        counts[w] = counts.get(w, 0) + 1
    return sorted(counts.items(), key=lambda kv: (-kv[1], kv[0]))[:k]


def sentences(text):
    """Split on . ! ? followed by whitespace, except after a known abbreviation."""
    out, start = [], 0
    for m in re.finditer(r"[.!?]+(?=\\s|$)", text):
        before = text[start:m.start()].split()
        last = before[-1].lower().rstrip(".") if before else ""
        if m.group() == "." and last in ABBREVIATIONS:
            continue
        chunk = text[start:m.end()].strip()
        if chunk:
            out.append(chunk)
        start = m.end()
    tail = text[start:].strip()
    if tail:
        out.append(tail)
    return out


def syllables(word):
    """Vowel groups, minus a silent final 'e' (but 'le' after a consonant counts), at least 1."""
    w = word.lower()
    groups = re.findall(r"[aeiouy]+", w)
    n = len(groups)
    if w.endswith("e") and not w.endswith("le") and n > 1:
        n -= 1
    return max(1, n)


def flesch(text):
    """Flesch reading ease, rounded to 1 decimal."""
    ws = words(text)
    ss = sentences(text)
    if not ws or not ss:
        return 0.0
    syl = sum(syllables(w) for w in ws)
    return round(206.835 - 1.015 * (len(ws) / len(ss)) - 84.6 * (syl / len(ws)), 1)
''',
    "cases.py": '''from .core import flesch, sentences, syllables, top_words

TEXTS = [
    "The cat sat. The cat ran! Did the dog see the cat? Mr. Smith said no.",
    "Simple is better than complex. Complex is better than complicated. Flat is better than nested.",
    "A table, a bottle, a little apple: make time for these e.g. lunch. Done",
]
WORDS = ["table", "make", "apple", "the", "rhythm", "queue", "little", "bottle", "time", "a"]


def run():
    return [[top_words(t, 4), sentences(t), flesch(t)] for t in TEXTS] + [[syllables(w) for w in WORDS]]
''',
    "tests/test_core.py": '''import unittest

from textstats.core import flesch, sentences, syllables, top_words


class CoreTest(unittest.TestCase):
    def test_top_words_ties_alphabetical(self):
        self.assertEqual(top_words("b a c b a", 3), [("a", 2), ("b", 2), ("c", 1)])

    def test_top_words_case_insensitive(self):
        self.assertEqual(top_words("Dog dog DOG cat", 1), [("dog", 3)])

    def test_sentences_abbreviation(self):
        self.assertEqual(sentences("Dr. No left. Then what?"), ["Dr. No left.", "Then what?"])

    def test_syllables(self):
        self.assertEqual([syllables(w) for w in ["make", "table", "the", "apple", "queue"]], [1, 2, 1, 2, 1])

    def test_flesch(self):
        self.assertEqual(flesch("The cat sat on the mat."), 116.1)


if __name__ == "__main__":
    unittest.main()
''',
    "bugs": [
        ('    return [w.lower() for w in WORD.findall(text)]', '    return WORD.findall(text)'),
        ("key=lambda kv: (-kv[1], kv[0])", "key=lambda kv: -kv[1]"),
        ('        if m.group() == "." and last in ABBREVIATIONS:\n            continue\n',
         '        if m.group() == "." and last in ABBREVIATIONS:\n            start = m.end()\n            continue\n'),
        ('    if w.endswith("e") and not w.endswith("le") and n > 1:', '    if w.endswith("e") and n > 1:'),
    ],
}

PKGS["inventory"] = {
    "core.py": '''"""Stock kept in lots; issues consume the oldest lot first (FIFO)."""
from dataclasses import dataclass, field


@dataclass
class Lot:
    received: int  # day number
    qty: int
    unit_cost: int  # cents


@dataclass
class Item:
    sku: str
    reorder_point: int
    lots: list = field(default_factory=list)

    def on_hand(self):
        return sum(lot.qty for lot in self.lots)

    def receive(self, day, qty, unit_cost):
        if qty <= 0:
            raise ValueError("qty must be positive")
        self.lots.append(Lot(day, qty, unit_cost))
        self.lots.sort(key=lambda lot: lot.received)

    def issue(self, qty):
        """Remove qty units, oldest lots first. Returns the cost of goods issued (cents)."""
        if qty > self.on_hand():
            raise ValueError(f"{self.sku}: only {self.on_hand()} on hand")
        cost = 0
        remaining = qty
        while remaining:
            lot = self.lots[0]
            take = min(lot.qty, remaining)
            cost += take * lot.unit_cost
            lot.qty -= take
            remaining -= take
            if lot.qty == 0:
                self.lots.pop(0)
        return cost

    def needs_reorder(self):
        """At or below the reorder point."""
        return self.on_hand() <= self.reorder_point

    def value(self):
        return sum(lot.qty * lot.unit_cost for lot in self.lots)


def process(items, events):
    """Apply events [("recv", sku, day, qty, cost) | ("issue", sku, qty)]; return COGS per sku and reorder list."""
    cogs = {sku: 0 for sku in items}
    for ev in events:
        if ev[0] == "recv":
            _, sku, day, qty, cost = ev
            items[sku].receive(day, qty, cost)
        elif ev[0] == "issue":
            _, sku, qty = ev
            cogs[sku] += items[sku].issue(qty)
        else:
            raise ValueError(f"unknown event {ev[0]}")
    reorder = sorted(sku for sku, item in items.items() if item.needs_reorder())
    return cogs, reorder
''',
    "cases.py": '''from .core import Item, process


def run():
    items = {"bolt": Item("bolt", 10), "nut": Item("nut", 5), "gear": Item("gear", 0)}
    events = [
        ("recv", "bolt", 3, 20, 15), ("recv", "bolt", 1, 10, 10), ("recv", "nut", 2, 8, 4),
        ("issue", "bolt", 15), ("issue", "nut", 3), ("recv", "gear", 5, 2, 900),
        ("recv", "bolt", 7, 5, 20), ("issue", "bolt", 12), ("issue", "gear", 2),
    ]
    cogs, reorder = process(items, events)
    return [cogs, reorder, {k: [v.on_hand(), v.value()] for k, v in items.items()}]
''',
    "tests/test_core.py": '''import unittest

from inventory.core import Item, process


class CoreTest(unittest.TestCase):
    def test_fifo_cost(self):
        it = Item("x", 0)
        it.receive(1, 5, 100)
        it.receive(2, 5, 200)
        self.assertEqual(it.issue(7), 5 * 100 + 2 * 200)
        self.assertEqual(it.on_hand(), 3)

    def test_receive_out_of_order(self):
        it = Item("x", 0)
        it.receive(9, 1, 50)
        it.receive(1, 1, 10)
        self.assertEqual(it.issue(1), 10)

    def test_reorder_at_point(self):
        it = Item("x", 4)
        it.receive(1, 4, 1)
        self.assertTrue(it.needs_reorder())

    def test_process(self):
        items = {"a": Item("a", 1)}
        cogs, reorder = process(items, [("recv", "a", 1, 3, 7), ("issue", "a", 2)])
        self.assertEqual((cogs, reorder), ({"a": 14}, ["a"]))


if __name__ == "__main__":
    unittest.main()
''',
    "bugs": [
        ("        self.lots.sort(key=lambda lot: lot.received)\n", ""),
        ("            lot = self.lots[0]", "            lot = self.lots[-1]"),
        ("            if lot.qty == 0:\n                self.lots.pop(0)", "            if lot.qty == 0:\n                self.lots.pop()"),
        ("        return self.on_hand() <= self.reorder_point", "        return self.on_hand() < self.reorder_point"),
    ],
}

PKGS["isoweek"] = {
    "core.py": '''"""ISO-8601 week numbers and business-day arithmetic, without datetime.isocalendar."""
import datetime as dt


def iso_week(d):
    """(iso_year, week) of date d. Week 1 is the week with the year's first Thursday; weeks start Monday."""
    thursday = d + dt.timedelta(days=3 - d.weekday())
    year = thursday.year
    first_thursday = dt.date(year, 1, 1)
    while first_thursday.weekday() != 3:
        first_thursday += dt.timedelta(days=1)
    week = (thursday - first_thursday).days // 7 + 1
    return year, week


def business_days(start, end, holidays=()):
    """Mon-Fri days in [start, end) that are not holidays. end before start counts negative."""
    if end < start:
        return -business_days(end, start, holidays)
    hol = set(holidays)
    n = 0
    d = start
    while d < end:
        if d.weekday() < 5 and d not in hol:
            n += 1
        d += dt.timedelta(days=1)
    return n


def add_business_days(start, n, holidays=()):
    """The date n business days after start (n >= 0); start itself is not counted."""
    hol = set(holidays)
    d = start
    while n > 0:
        d += dt.timedelta(days=1)
        if d.weekday() < 5 and d not in hol:
            n -= 1
    return d
''',
    "cases.py": '''import datetime as dt

from .core import add_business_days, business_days, iso_week

D = dt.date
DATES = [D(2026, 1, 1), D(2027, 1, 1), D(2026, 12, 31), D(2020, 12, 31), D(2021, 1, 3), D(2024, 12, 30), D(2026, 6, 15)]
HOL = [D(2026, 12, 25), D(2027, 1, 1)]


def run():
    return [
        [iso_week(d) for d in DATES],
        business_days(D(2026, 12, 21), D(2027, 1, 5), HOL),
        business_days(D(2026, 3, 9), D(2026, 3, 2)),
        add_business_days(D(2026, 12, 24), 3, HOL),
        add_business_days(D(2026, 10, 30), 0),
    ]
''',
    "tests/test_core.py": '''import datetime as dt
import unittest

from isoweek.core import add_business_days, business_days, iso_week

D = dt.date


class CoreTest(unittest.TestCase):
    def test_iso_week_year_boundary(self):
        self.assertEqual(iso_week(D(2021, 1, 3)), (2020, 53))
        self.assertEqual(iso_week(D(2024, 12, 30)), (2025, 1))

    def test_iso_week_plain(self):
        self.assertEqual(iso_week(D(2026, 6, 15)), (2026, 25))

    def test_business_days_half_open(self):
        self.assertEqual(business_days(D(2026, 11, 2), D(2026, 11, 9)), 5)

    def test_business_days_holiday(self):
        self.assertEqual(business_days(D(2026, 12, 21), D(2026, 12, 28), [D(2026, 12, 25)]), 4)

    def test_add_business_days_skips_weekend(self):
        self.assertEqual(add_business_days(D(2026, 10, 30), 1), D(2026, 11, 2))

    def test_add_business_days_skips_holiday(self):
        self.assertEqual(add_business_days(D(2026, 12, 24), 1, [D(2026, 12, 25)]), D(2026, 12, 28))


if __name__ == "__main__":
    unittest.main()
''',
    "bugs": [
        ("    thursday = d + dt.timedelta(days=3 - d.weekday())\n    year = thursday.year",
         "    thursday = d + dt.timedelta(days=3 - d.weekday())\n    year = d.year"),
        ("    while d < end:", "    while d <= end:"),
        ("        if d.weekday() < 5 and d not in hol:\n            n -= 1",
         "        if d.weekday() < 5:\n            n -= 1"),
    ],
}


def write_pkg(base, name, spec, buggy):
    pkg = base / "pkgs" / name / name
    (pkg / "tests").mkdir(parents=True, exist_ok=True)
    (pkg / "__init__.py").write_text("")
    (pkg / "tests" / "__init__.py").write_text("")
    (pkg / "selfcheck.py").write_text(SELFCHECK)
    (pkg / "__main__.py").write_text("from .selfcheck import main\n\nmain()\n")
    extra_core, extra_import, extra_expr, extra_bug = EXTRA[name]
    core = spec["core.py"] + extra_core
    if buggy:
        for old, new in spec["bugs"] + [extra_bug]:
            assert core.count(old) == 1, (name, old)
            core = core.replace(old, new)
    (pkg / "core.py").write_text(core)
    cases = spec["cases.py"].rstrip() + f"\n{extra_import}\n" + (
        '\n\ndef _items():\n    a, b, c = Item("a", 0), Item("b", 0), Item("c", 0)\n    a.receive(1, 3, 100)\n'
        '    a.receive(2, 1, 201)\n    c.receive(1, 2, 5)\n    c.receive(3, 4, 6)\n    c.issue(1)\n    return [a, b, c]\n'
        if name == "inventory" else "") + f"\n\n_base_run = run\n\n\ndef run():\n    return _base_run() + [{extra_expr}]\n"
    (pkg / "cases.py").write_text(cases)
    (pkg / "tests" / "test_core.py").write_text(spec["tests/test_core.py"])


def run_checks(base, name):
    cwd = base / "pkgs" / name
    t = subprocess.run([sys.executable, "-m", "unittest", "discover", "-s", name / pathlib.Path("tests"), "-t", "."],
                       cwd=cwd, capture_output=True, text=True)
    s = subprocess.run([sys.executable, "-m", f"{name}.selfcheck"], cwd=cwd, capture_output=True, text=True)
    return t.returncode, t.stderr[-300:], s.stdout.strip()


def main():
    for d in (OUT, REF):
        if d.exists():
            shutil.rmtree(d)
    expected = {}
    for name, spec in PKGS.items():
        write_pkg(REF, name, spec, buggy=False)
        rc, err, line = run_checks(REF, name)
        assert rc == 0, (name, err)
        expected[name] = line
        write_pkg(OUT, name, spec, buggy=True)
        rc, err, bline = run_checks(OUT, name)
        assert rc != 0 and bline != line, (name, "bugs not visible", bline)
    (OUT / "README.md").write_text(
        "# pkgs\n\nFour independent Python packages under `pkgs/<name>/<name>`. Run one package's tests from "
        "`pkgs/<name>`: `python3 -m unittest discover -s <name>/tests -t .`. Its self-check: "
        "`python3 -m <name>.selfcheck` (from `pkgs/<name>`).\n")
    (ROOT / "expected").mkdir(parents=True, exist_ok=True)
    (ROOT / "expected" / "fanout.json").write_text(json.dumps(expected, indent=1))
    print(json.dumps(expected, indent=1))


if __name__ == "__main__":
    main()
