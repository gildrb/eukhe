# doc_rows: what a read of a file shows (crates/eukhe-docs/src/read/mod.rs).
#
# Gate: a read that is not raw refuses a file that is not UTF-8 (a
# UTF-16 BOM, or no NUL byte in the sniffed head) and a binary file (a
# NUL byte in the sniffed head).
#
# View: Rust sends the projection of the file (bend/doc_lines.bend
# `Proj`: the BOM flag and each line's length and ending), the selector
# and two facts (the bytes are UTF-8; the file is over the size limit of
# a tag). The lines a read numbers are the addressable lines: the pieces
# of the file, but an empty last piece after a final `\n` is no line. A
# raw read counts every piece. The answer is the number of lines, the
# spans of lines shown (each with whether a gap marker comes before it),
# the notices, and whether the read gets a tag. Rust writes row i from
# line i of its projection.
#
# Window (no selector, or one range): a range that starts past the end
# shows nothing (notice: the line is beyond the end). Otherwise the lines
# from its start to its end (or the end of the file). A range with a
# start past line 1 also shows the line before it; a range with an end
# also shows the 3 lines after it (not raw). A range with an end that
# stops before the last line gets the notice of the lines that remain.
# Ranges (two or more): each range in the order given (the read tool's
# selector sorts and merges them first: crates/eukhe-docs/src/read/
# selector.rs); a range that starts past the end is dropped with its
# notice; the others are cut at the end of the file. A gap marker comes
# before every span but the first that does not start right after the
# span before it: a later span, an earlier one or an overlapping one
# (raw: before every span but the first).

import Base
import ./doc_lines.bend as Dl

# Gate
# ----

type Gate is Data:
  Go{}
  NotUtf8{}
  Binary{}

def gate.utf8(nul: Bool) -> Gate:
  match nul:
    case True{}:
      Binary{}
    case False{}:
      Go{}

def gate.bytes(utf16: Bool, nul: Bool) -> Gate:
  match utf16:
    case True{}:
      NotUtf8{}
    case False{}:
      match nul:
        case True{}:
          Binary{}
        case False{}:
          NotUtf8{}

# raw: the selector is raw; utf8: the bytes are UTF-8; utf16: they start
# with a UTF-16 BOM; nul: the sniffed head has a NUL byte
def gate(raw: Bool, utf8: Bool, utf16: Bool, nul: Bool) -> Gate:
  match raw:
    case True{}:
      Go{}
    case False{}:
      match utf8:
        case True{}:
          gate.utf8(nul)
        case False{}:
          gate.bytes(utf16, nul)

# Selectors
# ---------

# an inclusive range of lines (from 1); None: to the end of the file
type Range is Data:
  Range{start: Nat, end: Maybe<&2, Nat>}

type Sel is Data:
  Whole{}
  Raw{}
  Lines{ranges: List<&2, Range>, raw: Bool}

# Views
# -----

# lines start..end shown; gap: a gap marker comes before them
type Span is Data:
  Span{start: Nat, end: Nat, gap: Bool}

type Note is Data:
  Beyond{line: Nat}                           # a window starts past the end
  Remain{count: Nat, next: Nat}               # count lines remain from line next
  RangeBeyond{start: Nat, end: Maybe<&2, Nat>} # a range starts past the end
  TooBig{}                                    # over the size limit: no tag

type View is Data:
  View{total: Nat, raw: Bool, spans: List<&2, Span>, notes: List<&2, Note>, tag: Bool}

# Lines
# -----

def count.last(l: Dl.Line, n: Nat) -> Nat:
  match l:
    case Dl.Line{k, en}:
      match k:
        case 0n:
          n
        case 1n+j:
          1n+n

def count.go(rest: List<&2, Dl.Line>, l: Dl.Line, +n: Nat) -> Nat:
  match rest:
    case Nil{}:
      count.last(l, n)
    case m <> more:
      count.go(more, m, 1n+n)

# the addressable lines: every piece, but an empty last piece after
# another is no line
def count(ls: List<&2, Dl.Line>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case l <> rest:
      match rest:
        case Nil{}:
          1n
        case m <> more:
          count.go(more, m, 1n)

# the lines a read counts: every piece when raw
def total(raw: Bool, +ls: List<&2, Dl.Line>) -> Nat:
  match raw:
    case True{}:
      List.length(&2, Dl.Line, ls)
    case False{}:
      count(ls)

# Window
# ------

# the line before a range with a start past line 1
def lead() -> Nat:
  1n

# the lines after a range with an end
def trail() -> Nat:
  3n

def low(+a: Nat, +b: Nat) -> Nat:
  Bool.pick(Nat, Nat.is_le(a, b), a, b)

def span.if(ok: Bool, +s: Nat, +e: Nat) -> List<&2, Span>:
  match ok:
    case True{}:
      [Span{s, e, False{}}]
    case False{}:
      Nil{}

# lines s..e, none when e is before s
def span.of(+s: Nat, +e: Nat) -> List<&2, Span>:
  span.if(Nat.is_le(s, e), s, e)

def window.left(on: Bool, +e: Nat, +t: Nat) -> List<&2, Note>:
  match on:
    case True{}:
      [Remain{Nat.sub(t, e), 1n+e}]
    case False{}:
      Nil{}

def window.remain(on: Bool, +e: Nat, +t: Nat) -> List<&2, Note>:
  match on:
    case True{}:
      window.left(Nat.is_lt(e, t), e, t)
    case False{}:
      Nil{}

# rs: the first line wanted, from 0; re: the line after the last wanted;
# ex: the range has an end
def window.show(+raw: Bool, +rs: Nat, +re: Nat, ex: Bool, +t: Nat) -> List<&2, Span> & List<&2, Note>:
  +es = Bool.and(Bool.not(raw), Nat.is_lt(0n, rs))
  +ee = Bool.and(Bool.not(raw), ex)
  +s = Bool.pick(Nat, es, Nat.sub(rs, lead()), rs)
  +e = Bool.pick(Nat, ee, low(Nat.add(re, trail()), t), re)
  (span.of(1n+s, e), window.remain(ee, e, t))

def window.end(+rs: Nat, m: Maybe<&2, Nat>, +st: Nat, +t: Nat) -> Nat:
  match m:
    case None{}:
      t
    case Some{+en}:
      low(Nat.add(rs, 1n+Nat.sub(en, st)), t)

def window.in(ok: Bool, raw: Bool, +rs: Nat, +st: Nat, +m: Maybe<&2, Nat>, +t: Nat) -> List<&2, Span> & List<&2, Note>:
  match ok:
    case True{}:
      +ex = Maybe.is_some(&2, Nat, m)
      window.show(raw, rs, window.end(rs, m, st, t), ex, t)
    case False{}:
      (Nil{}, [Beyond{1n+rs}])

def window.at(raw: Bool, +st: Nat, m: Maybe<&2, Nat>, +t: Nat) -> List<&2, Span> & List<&2, Note>:
  +rs = Nat.sub(st, 1n)
  window.in(Nat.is_lt(rs, t), raw, rs, st, m, t)

def window(raw: Bool, r: Maybe<&2, Range>, +t: Nat) -> List<&2, Span> & List<&2, Note>:
  match r:
    case None{}:
      window.at(raw, 1n, None{}, t)
    case Some{x}:
      match x:
        case Range{st, m}:
          window.at(raw, st, m, t)

# Ranges
# ------

def ranges.gap(prev: Maybe<&2, Nat>, raw: Bool, +s: Nat) -> Bool:
  match prev:
    case None{}:
      False{}
    case Some{+pe}:
      match raw:
        case True{}:
          True{}
        case False{}:
          Bool.not(Nat.is_eq(1n+pe, s))

def ranges.cons(+sp: Span, r: List<&2, Span> & List<&2, Note>) -> List<&2, Span> & List<&2, Note>:
  match r:
    case (a, b):
      (sp <> a, b)

def ranges.note(+n: Note, r: List<&2, Span> & List<&2, Note>) -> List<&2, Span> & List<&2, Note>:
  match r:
    case (a, b):
      (a, n <> b)

def ranges.cut(m: Maybe<&2, Nat>, +t: Nat) -> Nat:
  match m:
    case None{}:
      t
    case Some{+k}:
      low(k, t)

def ranges.put(past: Bool, +st: Nat, m: Maybe<&2, Nat>, +en: Nat, gap: Bool, r: List<&2, Span> & List<&2, Note>) -> List<&2, Span> & List<&2, Note>:
  match past:
    case True{}:
      ranges.note(RangeBeyond{st, m}, r)
    case False{}:
      ranges.cons(Span{st, en, gap}, r)

# prev: the end of the span before (None: the first)
def ranges.go(xs: List<&2, Range>, +raw: Bool, +prev: Maybe<&2, Nat>, +t: Nat) -> List<&2, Span> & List<&2, Note>:
  match xs:
    case Nil{}:
      (Nil{}, Nil{})
    case x <> rest:
      match x:
        case Range{+st, +m}:
          +past = Nat.is_lt(t, st)
          +en = ranges.cut(m, t)
          ranges.put(past, st, m, en, ranges.gap(prev, raw, st), ranges.go(rest, raw, Bool.pick(Maybe<&2, Nat>, past, prev, Some{en}), t))

# View
# ----

def view.sel(s: Sel, +t: Nat) -> List<&2, Span> & List<&2, Note>:
  match s:
    case Whole{}:
      window(False{}, None{}, t)
    case Raw{}:
      (span.of(1n, t), Nil{})
    case Lines{xs, raw}:
      match xs:
        case Nil{}:
          window(raw, None{}, t)
        case x <> rest:
          match rest:
            case Nil{}:
              window(raw, Some{x}, t)
            case y <> more:
              ranges.go(x <> y <> more, raw, None{}, t)

def Sel.raw(s: Sel) -> Bool:
  match s:
    case Whole{}:
      False{}
    case Raw{}:
      True{}
    case Lines{xs, raw}:
      raw

def view.fin(+t: Nat, raw: Bool, r: List<&2, Span> & List<&2, Note>, utf8: Bool, over: Bool) -> View:
  match r:
    case (sp, ns):
      match over:
        case True{}:
          View{t, raw, sp, List.append(&2, Note, ns, [TooBig{}]), False{}}
        case False{}:
          View{t, raw, sp, ns, utf8}

# what a read of a file with projection p shows
def view(+s: Sel, utf8: Bool, over: Bool, p: Dl.Proj) -> View:
  match p:
    case Dl.Proj{b, +ls}:
      +raw = Sel.raw(s)
      +t = total(raw, ls)
      view.fin(t, raw, view.sel(s, t), utf8, over)
