"""Reference implementation of fixtures/sheet/SPEC.md (gen only; never shipped to the agent)."""
import csv
import re
import sys
from decimal import ROUND_HALF_UP, Decimal

NUM = re.compile(r"^[+-]?(\d+(\.\d*)?|\.\d+)([eE][+-]?\d+)?$")
REF = re.compile(r"\$?([A-Za-z]{1,3})\$?(\d+)")


class Err:
    def __init__(self, code):
        self.code = code

    def __eq__(self, other):
        return isinstance(other, Err) and other.code == self.code

    def __repr__(self):
        return self.code


DIV0, REFE, NAME, VALUE, CYCLE, PARSE = (Err(c) for c in ("#DIV/0!", "#REF!", "#NAME?", "#VALUE!", "#CYCLE!", "#PARSE!"))


class ParseError(Exception):
    pass


def norm(x):
    if isinstance(x, float) and x.is_integer():
        return int(x)
    return x


def literal(text):
    s = text.strip()
    if s == "":
        return None
    if NUM.match(s):
        return int(s) if re.fullmatch(r"[+-]?\d+", s) else norm(float(s))
    if text.startswith("'"):
        return text[1:]
    return text


def cell_name(col, row):
    col = col.upper()
    if len(col) != 1 or not 1 <= row <= 99:
        return None
    return f"{col}{row}"


# ------------------------------------------------------------------ tokens and parser

TOKEN = re.compile(r"""\s*(?:
    (?P<num>\d+(?:\.\d+)?)
  | (?P<str>"(?:[^"]|"")*")
  | (?P<range>\$?[A-Za-z]{1,3}\$?\d+\s*:\s*\$?[A-Za-z]{1,3}\$?\d+)
  | (?P<ref>\$?[A-Za-z]{1,3}\$?\d+(?![A-Za-z0-9_(]))
  | (?P<name>[A-Za-z_][A-Za-z0-9_.]*)
  | (?P<op><=|>=|<>|[-+*/^&=<>(),%])
)""", re.X)


def tokenize(src):
    pos, out = 0, []
    src = src.rstrip()
    while pos < len(src):
        m = TOKEN.match(src, pos)
        if not m or m.end() == pos:
            raise ParseError(src[pos:])
        kind = m.lastgroup
        out.append((kind, m.group(kind)))
        pos = m.end()
    return out


class Parser:
    def __init__(self, toks):
        self.t, self.i = toks, 0

    def peek(self, val=None):
        if self.i < len(self.t) and (val is None or self.t[self.i] == ("op", val)):
            return self.t[self.i]
        return None

    def take(self, val):
        if not self.peek(val):
            raise ParseError(val)
        self.i += 1

    def parse(self):
        e = self.comparison()
        if self.i != len(self.t):
            raise ParseError("trailing")
        return e

    def binary(self, ops, sub):
        e = sub()
        while self.peek() and self.peek()[0] == "op" and self.peek()[1] in ops:
            op = self.t[self.i][1]
            self.i += 1
            e = ("bin", op, e, sub())
        return e

    def comparison(self):
        return self.binary(("=", "<>", "<", ">", "<=", ">="), self.concat)

    def concat(self):
        return self.binary(("&",), self.additive)

    def additive(self):
        return self.binary(("+", "-"), self.term)

    def term(self):
        return self.binary(("*", "/"), self.unary)

    def unary(self):
        if self.peek("-"):
            self.i += 1
            return ("neg", self.unary())
        if self.peek("+"):
            self.i += 1
            return self.unary()
        return self.power()

    def power(self):
        base = self.postfix()
        if self.peek("^"):
            self.i += 1
            return ("bin", "^", base, self.unary())
        return base

    def postfix(self):
        e = self.primary()
        while self.peek("%"):
            self.i += 1
            e = ("pct", e)
        return e

    def primary(self):
        if self.i >= len(self.t):
            raise ParseError("end")
        kind, val = self.t[self.i]
        self.i += 1
        if kind == "num":
            return ("lit", norm(float(val)) if "." in val else int(val))
        if kind == "str":
            return ("lit", val[1:-1].replace('""', '"'))
        if kind == "ref":
            return ("ref", val)
        if kind == "range":
            raise ParseError("range outside a function")
        if kind == "name":
            if self.peek("("):
                self.i += 1
                args = []
                if not self.peek(")"):
                    while True:
                        if self.i < len(self.t) and self.t[self.i][0] == "range":
                            args.append(("range", self.t[self.i][1]))
                            self.i += 1
                        else:
                            args.append(self.comparison())
                        if self.peek(","):
                            self.i += 1
                            continue
                        break
                self.take(")")
                return ("call", val.upper(), args)
            if val.upper() in ("TRUE", "FALSE"):
                return ("lit", val.upper() == "TRUE")
            return ("name", val)
        if (kind, val) == ("op", "("):
            e = self.comparison()
            self.take(")")
            return e
        raise ParseError(val)


# ------------------------------------------------------------------ evaluation

def to_num(v):
    if isinstance(v, Err):
        return v
    if v is None:
        return 0
    if isinstance(v, bool):
        return int(v)
    if isinstance(v, (int, float)):
        return v
    s = v.strip()
    if NUM.match(s):
        return literal(s)
    return VALUE


def display(v):
    if v is None:
        return ""
    if isinstance(v, Err):
        return v.code
    if isinstance(v, bool):
        return "TRUE" if v else "FALSE"
    if isinstance(v, float):
        return f"{v:.10g}"
    return str(v)


def truthy(v):
    if isinstance(v, Err):
        return v
    if v is None:
        return False
    if isinstance(v, bool):
        return v
    if isinstance(v, (int, float)):
        return v != 0
    if v.upper() in ("TRUE", "FALSE"):
        return v.upper() == "TRUE"
    return VALUE


def compare(op, a, b):
    def key(v, other):
        if v is None:
            v = "" if isinstance(other, str) else 0
        if isinstance(v, bool):
            v = int(v)
        if isinstance(v, str):
            return (1, v.casefold())
        return (0, v)
    ka, kb = key(a, b), key(b, a)
    return {"=": ka == kb, "<>": ka != kb, "<": ka < kb, ">": ka > kb, "<=": ka <= kb, ">=": ka >= kb}[op]


class Sheet:
    def __init__(self, cells):
        self.src = {k.upper(): v for k, v in cells.items()}
        self.memo = {}
        self.busy = set()

    def cell(self, name):
        if name in self.memo:
            return self.memo[name]
        if name in self.busy:
            return CYCLE
        text = self.src.get(name)
        if text is None:
            return None
        if not text.startswith("="):
            v = literal(text)
        else:
            self.busy.add(name)
            try:
                tree = Parser(tokenize(text[1:])).parse()
            except ParseError:
                v = PARSE
            else:
                v = self.ev(tree)
                if v is None:
                    v = 0
            self.busy.discard(name)
        self.memo[name] = v
        return v

    def ref(self, text):
        m = REF.fullmatch(text.strip())
        name = cell_name(m.group(1), int(m.group(2)))
        return REFE if name is None else self.cell(name)

    def range_values(self, text):
        a, b = (REF.fullmatch(p.strip()) for p in text.split(":"))
        na, nb = cell_name(a.group(1), int(a.group(2))), cell_name(b.group(1), int(b.group(2)))
        if na is None or nb is None:
            return REFE
        c1, c2 = sorted((na[0], nb[0]))
        r1, r2 = sorted((int(na[1:]), int(nb[1:])))
        return [self.cell(f"{chr(c)}{r}") for r in range(r1, r2 + 1) for c in range(ord(c1), ord(c2) + 1)]

    def ev(self, e):
        kind = e[0]
        if kind == "lit":
            return e[1]
        if kind == "ref":
            return self.ref(e[1])
        if kind == "name":
            return NAME
        if kind == "neg":
            v = to_num(self.ev(e[1]))
            return v if isinstance(v, Err) else norm(-v)
        if kind == "pct":
            v = to_num(self.ev(e[1]))
            return v if isinstance(v, Err) else norm(v / 100)
        if kind == "bin":
            return self.binop(e[1], e[2], e[3])
        if kind == "call":
            return self.call(e[1], e[2])
        raise AssertionError(kind)

    def binop(self, op, le, re_):
        a = self.ev(le)
        if isinstance(a, Err):
            return a
        b = self.ev(re_)
        if isinstance(b, Err):
            return b
        if op in ("=", "<>", "<", ">", "<=", ">="):
            return compare(op, a, b)
        if op == "&":
            return display(a) + display(b)
        a, b = to_num(a), to_num(b)
        if isinstance(a, Err):
            return a
        if isinstance(b, Err):
            return b
        if op == "+":
            return norm(a + b)
        if op == "-":
            return norm(a - b)
        if op == "*":
            return norm(a * b)
        if op == "/":
            return DIV0 if b == 0 else norm(a / b)
        if op == "^":
            try:
                return norm(float(a) ** b) if not (isinstance(a, int) and isinstance(b, int) and b >= 0) else a ** b
            except (ZeroDivisionError, OverflowError):
                return DIV0
        raise AssertionError(op)

    def collect(self, args, numbers_only=True, ignore_errors=False):
        """Values of args: direct args coerced to numbers; ranges give their numbers (text, bools, empty skipped)."""
        out = []
        for a in args:
            if a[0] == "range":
                vals = self.range_values(a[1])
                if isinstance(vals, Err):
                    return vals
                for v in vals:
                    if isinstance(v, Err):
                        if ignore_errors:
                            continue
                        return v
                    if isinstance(v, (int, float)) and not isinstance(v, bool):
                        out.append(v)
            else:
                v = self.ev(a)
                if isinstance(v, Err) and ignore_errors:
                    continue
                v = to_num(v)
                if isinstance(v, Err):
                    if ignore_errors:
                        continue
                    return v
                out.append(v)
        return out

    def call(self, fn, args):
        if fn in ("SUM", "MIN", "MAX", "AVERAGE", "COUNT"):
            vals = self.collect(args, ignore_errors=(fn == "COUNT"))
            if isinstance(vals, Err):
                return vals
            if fn == "SUM":
                return norm(sum(vals))
            if fn == "COUNT":
                return len(vals)
            if fn == "AVERAGE":
                return DIV0 if not vals else norm(sum(vals) / len(vals))
            if not vals:
                return 0
            return norm(min(vals) if fn == "MIN" else max(vals))
        if fn == "IF":
            if len(args) not in (2, 3) or any(a[0] == "range" for a in args):
                return VALUE
            c = truthy(self.ev(args[0]))
            if isinstance(c, Err):
                return c
            if c:
                return self.ev(args[1])
            return self.ev(args[2]) if len(args) == 3 else False
        if fn in ("AND", "OR"):
            bools = []
            for a in args:
                vals = self.range_values(a[1]) if a[0] == "range" else [self.ev(a)]
                if isinstance(vals, Err):
                    return vals
                for v in vals:
                    if isinstance(v, Err):
                        return v
                    if a[0] == "range" and (v is None or isinstance(v, str)):
                        continue
                    t = truthy(v)
                    if isinstance(t, Err):
                        return t
                    bools.append(t)
            if not bools:
                return VALUE
            return all(bools) if fn == "AND" else any(bools)
        if fn == "NOT":
            if len(args) != 1 or args[0][0] == "range":
                return VALUE
            t = truthy(self.ev(args[0]))
            return t if isinstance(t, Err) else not t
        if fn == "ROUND":
            if len(args) not in (1, 2) or any(a[0] == "range" for a in args):
                return VALUE
            x = to_num(self.ev(args[0]))
            n = to_num(self.ev(args[1])) if len(args) == 2 else 0
            for v in (x, n):
                if isinstance(v, Err):
                    return v
            q = Decimal(1).scaleb(-int(n))
            return norm(float(Decimal(repr(x)).quantize(q, rounding=ROUND_HALF_UP)))
        if fn in ("LEN", "UPPER", "LOWER"):
            if len(args) != 1 or args[0][0] == "range":
                return VALUE
            v = self.ev(args[0])
            if isinstance(v, Err):
                return v
            s = display(v)
            return len(s) if fn == "LEN" else (s.upper() if fn == "UPPER" else s.lower())
        if fn == "CONCAT":
            parts = []
            for a in args:
                vals = self.range_values(a[1]) if a[0] == "range" else [self.ev(a)]
                if isinstance(vals, Err):
                    return vals
                for v in vals:
                    if isinstance(v, Err):
                        return v
                    parts.append(display(v))
            return "".join(parts)
        return NAME


def evaluate(cells):
    sheet = Sheet(cells)
    out = {}
    for name in cells:
        v = sheet.cell(name.upper())
        out[name] = v.code if isinstance(v, Err) else v
    return out


def main(argv=None):
    argv = sys.argv[1:] if argv is None else argv
    with open(argv[0], newline="") as fh:
        rows = list(csv.reader(fh))
    cells = {f"{chr(65 + c)}{r + 1}": v for r, row in enumerate(rows) for c, v in enumerate(row) if v != ""}
    vals = Sheet(cells)
    w = csv.writer(sys.stdout, lineterminator="\n")
    for r, row in enumerate(rows):
        w.writerow([display(vals.cell(f"{chr(65 + c)}{r + 1}")) if v != "" else "" for c, v in enumerate(row)])
