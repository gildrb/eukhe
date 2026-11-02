#!/usr/bin/env python3
"""Fixture `sheet`: implement a spreadsheet evaluator from SPEC.md (R1-R27); hidden tests per requirement."""
import pathlib
import re
import shutil
import subprocess
import sys

ROOT = pathlib.Path(sys.argv[1]).resolve()  # the bench data dir
OUT = ROOT / "fixtures" / "sheet"
HIDDEN = ROOT / "hidden" / "sheet"

SPEC = r'''# sheet

`sheet.evaluate(cells)` takes a dict from cell name to the cell's text and returns a dict with the same keys,
each mapped to the cell's value: an `int`, a `float`, a `str`, a `bool`, `None`, or an error, given as one of
the strings `"#DIV/0!"`, `"#REF!"`, `"#NAME?"`, `"#VALUE!"`, `"#CYCLE!"`, `"#PARSE!"`. Cell names are a column
letter A-Z and a row 1-99, in any case; the output keeps the input's keys.

Every requirement below must hold. Examples are normative.

- **R1 Numbers.** A cell whose text, with surrounding whitespace removed, matches
  `[+-]?(\d+(\.\d*)?|\.\d+)([eE][+-]?\d+)?` is a number: an `int` when it is only an optional sign and digits,
  otherwise a `float`, except that whole-number results are ints (R6). `" 7 "` is 7, `"3.50"` is 3.5, `"1e3"`
  is 1000, `"-.5"` is -0.5.
- **R2 Text.** Any other cell that does not start with `=` is text, kept exactly as written (not stripped).
  A leading apostrophe is dropped and the rest is text even if it looks like a number: `"'123"` is `"123"`.
  A plain cell `"TRUE"` is the text `"TRUE"`.
- **R3 Empty.** A cell whose text is empty or only whitespace is `None`. A reference to an empty cell, or to a
  cell missing from the input, is 0 in arithmetic and in comparisons with a number, and `""` in concatenation
  and in comparisons with text. A formula whose result is such an empty reference (`=A1`, A1 empty) is 0.
- **R4 Formulas.** A cell starting with `=` is a formula. Operators `+ - * /` have the usual precedence and
  are left associative; parentheses group; unary `+` and `-` are allowed. Number literals in formulas are
  digits with an optional fraction (`12`, `0.5`), without exponent.
- **R5 Power.** `^` is right associative and binds tighter than unary minus: `=-2^2` is -4, `=2^3^2` is 512,
  `=2^-1` is 0.5.
- **R6 Whole numbers.** A numeric result that is a whole number is an `int` (`=6/3` is 2, `=2.5*2` is 5);
  otherwise it is a `float` (`=7/2` is 3.5).
- **R7 References.** `A1`, `b7`, `Z99`: case-insensitive. A `$` before the column and/or the row is allowed and
  ignored (`$A$1`, `A$1`).
- **R8** Division by zero is `"#DIV/0!"`.
- **R9 Errors propagate.** An operator or function that receives an error returns it. A binary operator
  evaluates its left operand first, and the left error wins.
- **R10** A reference whose column is not one letter A-Z or whose row is not 1-99 (`AA1`, `A100`, `A0`) is
  `"#REF!"`, in a range too.
- **R11 Cycles.** A cell whose evaluation needs its own value, directly or through other cells, is
  `"#CYCLE!"`; by R9 so is every cell that needs the value of a `"#CYCLE!"` cell. Only references that are
  actually evaluated count (an `IF` branch not taken is not evaluated, R18).
- **R12 Ranges.** `A1:B3` is the rectangle between two corners given in either order (`B3:A1` is the same
  range), read row by row, left to right. A range is allowed only as a whole function argument; anywhere else
  the formula is `"#PARSE!"`.
- **R13 Aggregates.** `SUM`, `MIN`, `MAX`, `AVERAGE`, `COUNT` take any number of arguments, each a range or an
  expression. An expression argument is converted to a number as in arithmetic (R20; text that is not a number
  is `"#VALUE!"`, TRUE is 1, empty is 0). In a range only number cells count: text, booleans and empty cells
  are skipped, and an error is returned. `COUNT` counts the numbers it gets and skips errors of both kinds of
  argument (non-numeric text included) instead of returning them. `MIN`/`MAX` of no numbers is 0; `AVERAGE`
  of no numbers is `"#DIV/0!"`.
- **R14 Names.** Function names are case-insensitive. An unknown function is `"#NAME?"`, and so is a bare name
  that is not a function call, a reference, `TRUE` or `FALSE`.
- **R15 Strings.** String literals use double quotes; a doubled quote inside is one quote:
  `="say ""hi"""` is `say "hi"`.
- **R16 Concatenation.** `&` joins texts. Precedence, lowest to highest: comparisons, `&`, `+ -`, `* /`, unary
  `-`, `^`, postfix `%`. A value becomes text as: int as its digits, float as Python `format(x, ".10g")`,
  booleans as `TRUE`/`FALSE`, empty as `""`.
- **R17 Comparisons.** `= <> < > <= >=` give a bool. Numbers (and booleans, as 1 and 0) compare by value; texts
  compare case-insensitively (`str.casefold`); any number is less than any text. Comparisons are left
  associative: `=1<2=TRUE` is TRUE.
- **R18 IF.** `IF(cond, then[, else])` evaluates only the chosen branch; a missing else gives FALSE. `cond`: a
  number is true when non-zero; booleans as themselves; the texts `"TRUE"`/`"FALSE"` in any case; empty is
  false; other text is `"#VALUE!"`. A wrong number of arguments, or a range argument, is `"#VALUE!"`.
- **R19 Logic.** `AND(...)` and `OR(...)` take expressions or ranges; each value is read as an IF condition;
  inside a range, text and empty cells are skipped. No values at all is `"#VALUE!"`. `NOT(x)` negates one value.
- **R20 Conversion in arithmetic.** Empty is 0, TRUE/FALSE are 1/0, text that is a number by R1 (after
  stripping) is that number, other text is `"#VALUE!"`.
- **R21 ROUND.** `ROUND(x[, n])` rounds to n decimals (default 0; a negative n rounds to tens, hundreds, ...),
  halves away from zero, working on the shortest decimal form of x: `ROUND(1.005, 2)` is 1.01, `ROUND(2.5)` is
  3, `ROUND(-2.5)` is -3, `ROUND(1234, -2)` is 1200.
- **R22 Text functions.** `LEN(x)`, `UPPER(x)`, `LOWER(x)` work on x converted to text (R16). `CONCAT(...)`
  joins its arguments converted to text; a range gives all its cells in range order, empty ones as `""`.
- **R23** `TRUE` and `FALSE` (any case) are boolean literals in formulas.
- **R24 Spaces.** Spaces are allowed anywhere between the tokens of a formula, including right after `=` and
  at the end.
- **R25 Percent.** Postfix `%` divides by 100: `=50%` is 0.5, `=10%*200` is 20.
- **R26 Parse errors.** A formula that does not parse (unbalanced parentheses, a dangling operator, an unknown
  character, `=` alone) is `"#PARSE!"`.
- **R27 CLI.** `python3 -m sheet grid.csv` reads a CSV grid (line r is row r, the c-th field is column A, B,
  ...), evaluates it, and prints the same grid as CSV with `\n` line ends: each non-empty cell replaced by its
  value as text (R16; errors as their code), empty cells left empty.
'''

STUB = '''"""A spreadsheet evaluator. See SPEC.md. So far only literal cells (R1-R3) work."""
import re

NUM = re.compile(r"^[+-]?(\\d+(\\.\\d*)?|\\.\\d+)([eE][+-]?\\d+)?$")


def _literal(text):
    s = text.strip()
    if s == "":
        return None
    if NUM.match(s):
        if re.fullmatch(r"[+-]?\\d+", s):
            return int(s)
        x = float(s)
        return int(x) if x.is_integer() else x
    if text.startswith("'"):
        return text[1:]
    return text


def evaluate(cells):
    out = {}
    for name, text in cells.items():
        if text.startswith("="):
            raise NotImplementedError("formulas")
        out[name] = _literal(text)
    return out


def main(argv=None):
    raise NotImplementedError("CLI")
'''

VISIBLE = '''import unittest

from sheet import evaluate


class LiteralTest(unittest.TestCase):
    def test_numbers_and_text(self):
        self.assertEqual(evaluate({"A1": " 7 ", "A2": "3.50", "A3": "'123", "A4": "hi", "A5": " "}),
                         {"A1": 7, "A2": 3.5, "A3": "123", "A4": "hi", "A5": None})


if __name__ == "__main__":
    unittest.main()
'''

HIDDEN_TESTS = r'''import os
import subprocess
import sys
import tempfile
import unittest

from sheet import evaluate


def ev(**cells):
    return evaluate(cells)


def one(formula, **cells):
    return evaluate({"Z99": formula, **cells})["Z99"]


def same(test, got, want):
    test.assertEqual((type(got).__name__, got), (type(want).__name__, want))


class R01(unittest.TestCase):
    def test(self):
        out = ev(A1=" 7 ", A2="3.50", A3="1e3", A4="-.5", A5="+4", A6="2.0")
        for k, want in {"A1": 7, "A2": 3.5, "A3": 1000, "A4": -0.5, "A5": 4, "A6": 2}.items():
            same(self, out[k], want)


class R02(unittest.TestCase):
    def test(self):
        self.assertEqual(ev(A1="'123", A2="TRUE", A3="  hi ", A4="1 2", A5="'=1"),
                         {"A1": "123", "A2": "TRUE", "A3": "  hi ", "A4": "1 2", "A5": "=1"})


class R03(unittest.TestCase):
    def test(self):
        self.assertEqual(ev(A1="", A2="  ", B1="=A1", B2="=A1+1", B3='=A1&"x"', B4="=Q7", B5='=A1=""', B6="=A1=0"),
                         {"A1": None, "A2": None, "B1": 0, "B2": 1, "B3": "x", "B4": 0, "B5": True, "B6": True})


class R04(unittest.TestCase):
    def test(self):
        for f, want in [("=1+2*3", 7), ("=(1+2)*3", 9), ("=10-4-3", 3), ("=8/4/2", 1), ("=-(2+3)", -5),
                        ("=+5", 5), ("=1.5+1.25", 2.75), ("=2*-3", -6)]:
            same(self, one(f), want)


class R05(unittest.TestCase):
    def test(self):
        for f, want in [("=-2^2", -4), ("=2^3^2", 512), ("=2^-1", 0.5), ("=(-2)^2", 4), ("=3*2^2", 12)]:
            same(self, one(f), want)


class R06(unittest.TestCase):
    def test(self):
        for f, want in [("=6/3", 2), ("=2.5*2", 5), ("=7/2", 3.5), ("=0.5+0.5", 1), ("=1/4", 0.25)]:
            same(self, one(f), want)


class R07(unittest.TestCase):
    def test(self):
        self.assertEqual(ev(A1="5", B7="2", Z98="1", C1="=a1+$B$7+B$7+$b7+Z98"), {"A1": 5, "B7": 2, "Z98": 1, "C1": 12})


class R08(unittest.TestCase):
    def test(self):
        self.assertEqual([one("=1/0"), one("=1/A1", A1=""), one("=5/(2-2)")], ["#DIV/0!"] * 3)


class R09(unittest.TestCase):
    def test(self):
        self.assertEqual([one("=1/0+AA1"), one("=AA1+1/0"), one("=(1/0)&\"x\""), one("=SUM(1,1/0)"),
                          one("=A1*2", A1="=1/0"), one("=-A1", A1="=foo(1)")],
                         ["#DIV/0!", "#REF!", "#DIV/0!", "#DIV/0!", "#DIV/0!", "#NAME?"])


class R10(unittest.TestCase):
    def test(self):
        self.assertEqual([one("=AA1"), one("=A100"), one("=A0"), one("=SUM(A1:A100)"), one("=A99+0")],
                         ["#REF!", "#REF!", "#REF!", "#REF!", 0])


class R11(unittest.TestCase):
    def test(self):
        out = ev(A1="=B1+1", B1="=A1", C1="=A1*0", D1="=D1", E1="=IF(TRUE, 3, E2)", E2="=E1", F1="7")
        self.assertEqual(out, {"A1": "#CYCLE!", "B1": "#CYCLE!", "C1": "#CYCLE!", "D1": "#CYCLE!", "E1": 3,
                               "E2": 3, "F1": 7})


class R12(unittest.TestCase):
    def test(self):
        cells = {"A1": "1", "B1": "2", "A2": "3", "B2": "4"}
        self.assertEqual([one("=SUM(B2:A1)", **cells), one('=CONCAT(A1:B2)', **cells), one("=A1:B2", **cells),
                          one("=SUM(A1:B2)+1", **cells), one("=SUM( A1 : B1 )", **cells)],
                         [10, "1234", "#PARSE!", 11, 3])


class R13(unittest.TestCase):
    def test(self):
        cells = {"A1": "1", "A2": "x", "A3": "=TRUE", "A4": "", "A5": "4", "B1": "=1/0", "C1": "'5"}
        got = [one(f, **cells) for f in ["=SUM(A1:A5)", "=SUM(A1:A5, 2, TRUE)", '=SUM("3")', '=SUM("x")',
                                          "=MIN(A1:A5)", "=MAX(A1:A5, 9)", "=AVERAGE(A1:A5)", "=AVERAGE(A2:A4)",
                                          "=COUNT(A1:B1)", '=COUNT(A1:A5, "x", 1/0, 3)', "=SUM(A1:B1)",
                                          "=MIN(A2:A4)", "=SUM(C1)", "=SUM(C1:C1)", "=AVERAGE(1, 2)"]]
        self.assertEqual(got, [5, 8, 3, "#VALUE!", 1, 9, 2.5, "#DIV/0!", 1, 3, "#DIV/0!", 0, 5, 0, 1.5])


class R14(unittest.TestCase):
    def test(self):
        self.assertEqual([one("=sum(1,2)"), one("=Max(1,5)"), one("=NOPE(1)"), one("=foo"), one("=foo+1")],
                         [3, 5, "#NAME?", "#NAME?", "#NAME?"])


class R15(unittest.TestCase):
    def test(self):
        self.assertEqual([one('="say ""hi"""'), one('=""'), one('="a,b"&"c"')], ['say "hi"', "", "a,bc"])


class R16(unittest.TestCase):
    def test(self):
        self.assertEqual([one('="n="&1+2'), one('=1&2'), one('=0.1+0.2&""'), one('=TRUE&"!"'), one('=1/3&""'),
                          one('="x"&A1', A1=""), one('=2.50&""')],
                         ["n=3", "12", "0.3", "TRUE!", "0.3333333333", "x", "2.5"])


class R17(unittest.TestCase):
    def test(self):
        got = [one(f) for f in ['=1<2', '=2<=2', '="abc"="ABC"', '="a"<"B"', '=9<"1"', '=TRUE=1', '=1<2=TRUE',
                                '=3<>3', '="b">"a"', '="10"<"9"', '=1+1=2']]
        self.assertEqual(got, [True, True, True, True, True, True, True, False, True, True, True])



class R18(unittest.TestCase):
    def test(self):
        got = [one(f, A1="") for f in ["=IF(1, 2, 3)", "=IF(0, 2, 3)", '=IF("true", 2, 1/0)', "=IF(FALSE, 1/0, 4)",
                                       "=IF(0, 1)", "=IF(A1, 1, 2)", '=IF("x", 1, 2)', "=IF(1)", "=IF(1/0, 1, 2)",
                                       "=IF(1, 2, 3, 4)", "=IF(A1:A2, 1, 2)"]]
        self.assertEqual(got, [2, 3, 2, 4, False, 2, "#VALUE!", "#VALUE!", "#DIV/0!", "#VALUE!", "#VALUE!"])


class R19(unittest.TestCase):
    def test(self):
        cells = {"A1": "1", "A2": "x", "A3": "", "A4": "=FALSE"}
        got = [one(f, **cells) for f in ["=AND(1, TRUE)", "=AND(1, 0)", "=OR(0, FALSE)", "=OR(0, 2)", "=AND(A1:A3)",
                                          "=AND(A1:A4)", "=OR(A2:A3)", '=AND("x")', "=NOT(0)", "=NOT(1)",
                                          '=NOT("false")', "=AND()"]]
        self.assertEqual(got, [True, False, False, True, True, False, "#VALUE!", "#VALUE!", True, False, True,
                               "#VALUE!"])


class R20(unittest.TestCase):
    def test(self):
        got = [one(f, A1=" 12 ", A2="abc", A3="") for f in ["=A1+1", "=A2+1", "=A3*5+1", "=TRUE+TRUE", '="3"*"4"',
                                                            '="1e2"+0', "=-A2"]]
        self.assertEqual(got, [13, "#VALUE!", 1, 2, 12, 100, "#VALUE!"])


class R21(unittest.TestCase):
    def test(self):
        for f, want in [("=ROUND(1.005, 2)", 1.01), ("=ROUND(2.5)", 3), ("=ROUND(-2.5)", -3), ("=ROUND(1234, -2)", 1200),
                        ("=ROUND(2.345, 2)", 2.35), ("=ROUND(7)", 7), ("=ROUND(-1.25, 1)", -1.3)]:
            same(self, one(f), want)
        self.assertEqual(one('=ROUND("x")'), "#VALUE!")


class R22(unittest.TestCase):
    def test(self):
        cells = {"A1": "ab", "B1": "", "C1": "3"}
        self.assertEqual([one(f, **cells) for f in ['=LEN("hello")', "=LEN(1/4)", '=UPPER("aBc")', "=LOWER(TRUE)",
                                                    "=CONCAT(A1:C1, 1, \"-\")", "=CONCAT()", "=LEN(B1)"]],
                         [5, 4, "ABC", "true", "ab31-", "", 0])


class R23(unittest.TestCase):
    def test(self):
        self.assertEqual([one("=TRUE"), one("=false"), one("=True+1")], [True, False, 2])


class R24(unittest.TestCase):
    def test(self):
        self.assertEqual([one("=  1 +  2 *3  "), one("= SUM( 1 , 2 ) "), one("= - 2 ^ 2")], [7, 3, -4])


class R25(unittest.TestCase):
    def test(self):
        for f, want in [("=50%", 0.5), ("=10%*200", 20), ("=200*10%", 20), ("=-50%", -0.5), ("=2^200%", 4)]:
            same(self, one(f), want)


class R26(unittest.TestCase):
    def test(self):
        self.assertEqual([one(f) for f in ["=", "=(1+2", "=1+", "=1+2)", "=1 # 2", "=SUM(1,", "=.5"]],
                         ["#PARSE!"] * 7)


class R27(unittest.TestCase):
    def test(self):
        with tempfile.NamedTemporaryFile("w", suffix=".csv", delete=False, newline="") as fh:
            fh.write('1,2,=A1+B1\n"=""a,""&1",,=1/0\n=0.1+0.2,=TRUE,x\n')
        try:
            r = subprocess.run([sys.executable, "-m", "sheet", fh.name], capture_output=True, text=True)
        finally:
            os.unlink(fh.name)
        self.assertEqual((r.returncode, r.stdout), (0, '1,2,3\n"a,1",,#DIV/0!\n0.3,TRUE,x\n'))


if __name__ == "__main__":
    unittest.main()
'''


def write(base, files):
    if base.exists():
        shutil.rmtree(base)
    for rel, text in files.items():
        p = base / rel
        p.parent.mkdir(parents=True, exist_ok=True)
        p.write_text(text)


def failures(base):
    t = base / "hidden_sheet_test.py"
    t.write_text(HIDDEN_TESTS)
    r = subprocess.run([sys.executable, "-B", "-m", "unittest", "-v", "hidden_sheet_test"], cwd=base,
                       capture_output=True, text=True)
    t.unlink()
    return sorted({m.group() for ln in r.stderr.splitlines() if ln.endswith(("FAIL", "ERROR"))
                   for m in [re.search(r"R\d\d", ln)] if m}), r.stderr


def main():
    files = {"SPEC.md": SPEC, "sheet/__init__.py": STUB, "sheet/__main__.py": "from . import main\n\nmain()\n",
             "tests/__init__.py": "", "tests/test_basic.py": VISIBLE,
             "AGENTS.md": "Run tests with `python3 -m unittest` from the repo root. Standard library only.\n"}
    write(OUT, files)
    ref = ROOT / "ref" / "sheet"
    write(ref, {**files, "sheet/__init__.py": pathlib.Path(__file__).with_name("sheet_ref.py").read_text()})
    fails, err = failures(ref)
    assert not fails, err[-4000:]
    fails, _ = failures(OUT)
    print("stub fails:", fails)
    HIDDEN.mkdir(parents=True, exist_ok=True)
    (HIDDEN / "hidden_sheet_test.py").write_text(HIDDEN_TESTS)
    r = subprocess.run([sys.executable, "-B", "-m", "unittest"], cwd=OUT, capture_output=True, text=True)
    assert r.returncode == 0, r.stderr
    print("sheet ok")


if __name__ == "__main__":
    main()
