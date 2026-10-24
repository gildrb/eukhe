# eukhe: the proof of LAW rows_gap_marks_every_jump
#
# The read is the rule (LAW rows_view_shows). A window shows at most one
# span, with no marker. Ranges are put in order, each after the span that
# ended at prev; a range past the end shows nothing and keeps prev; a
# shown range gets the rule's marker and the next one is put after it.

import Base
import ../../bend/doc_lines.bend as Dl
import ../../bend/doc_rows.bend as Dr
import ../../laws/doc_rows.bend as DocRows
import ./rows_view_shows.bend as Rvs

def gm.fst(r: List<&2, Dr.Span> & List<&2, Dr.Note>) -> List<&2, Dr.Span>:
  match r:
    case (a, b):
      a

def gm.and_t(a: Bool, b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def gm.same_refl(b: Bool) -> {DocRows.rows.Same(b, b) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the marker the rule puts before a span is the one rows.Marked gives it
def gm.same(raw: Bool, prev: Maybe<&2, Nat>, st: Nat) -> {DocRows.rows.Same(Bool.and(Maybe.is_some(&2, Nat, prev), Bool.or(raw, Bool.not(Nat.is_eq(Nat.add(Maybe.default(&2, Nat, prev, 0n), 1n), st)))), DocRows.rows.Marked(raw, prev, st)) == True{} : Bool}:
  match prev:
    case None{}:
      {==}
    case Some{pe}:
      gm.same_refl(Bool.or(raw, Bool.not(Nat.is_eq(Nat.add(pe, 1n), st))))

# a span under a flag, alone: no marker
def gm.span(raw: Bool, c: Bool, f: Nat, l: Nat) -> {DocRows.rows.Marks(DocRows.rows.If(List<&2, Dr.Span>, c, [Dr.Span{f, l, False{}}], Nil{}), raw, None{}) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a window with an end
def gm.ends(r: Bool, raw: Bool, +sf: Nat, +want: Nat, +t: Nat) -> {DocRows.rows.Marks(gm.fst(DocRows.rows.Window.ends(raw, sf, want, t)), r, None{}) == True{} : Bool}:
  match raw:
    case True{}:
      gm.span(r, Nat.is_le(sf, want), sf, want)
    case False{}:
      gm.span(r, Nat.is_le(sf, Nat.min(Nat.add(want, 3n), t)), sf, Nat.min(Nat.add(want, 3n), t))

# a window from line f that starts in the file
def gm.in(r: Bool, +raw: Bool, +f: Nat, m: Maybe<&2, Nat>, +st: Nat, +t: Nat) -> {DocRows.rows.Marks(gm.fst(DocRows.rows.Window.in(raw, f, m, st, t)), r, None{}) == True{} : Bool}:
  match m:
    case None{}:
      gm.span(r, Nat.is_le(DocRows.rows.Window.first(raw, f), t), DocRows.rows.Window.first(raw, f), t)
    case Some{+en}:
      gm.ends(r, raw, DocRows.rows.Window.first(raw, f), Nat.min(Nat.add(f, Nat.sub(en, st)), t), t)

def gm.pick(c: Bool, r: Bool, +raw: Bool, +f: Nat, +m: Maybe<&2, Nat>, +st: Nat, +t: Nat) -> {DocRows.rows.Marks(gm.fst(DocRows.rows.Pick(List<&2, Dr.Span> & List<&2, Dr.Note>, c, (Nil{}, [Dr.Beyond{f}]), DocRows.rows.Window.in(raw, f, m, st, t))), r, None{}) == True{} : Bool}:
  match c:
    case True{}:
      {==}
    case False{}:
      gm.in(r, raw, f, m, st, t)

# a window shows at most one span, with no marker
def gm.win(r: Bool, +raw: Bool, +st: Nat, +m: Maybe<&2, Nat>, +t: Nat) -> {DocRows.rows.Marks(gm.fst(DocRows.rows.Window(raw, st, m, t)), r, None{}) == True{} : Bool}:
  gm.pick(Nat.is_lt(t, Nat.max(st, 1n)), r, raw, Nat.max(st, 1n), m, st, t)

# one range, before the ranges after it (shown after the span that ended
# at L when it is shown: c false)
def gm.step_c(c: Bool, +raw: Bool, +prev: Maybe<&2, Nat>, +st: Nat, +m: Maybe<&2, Nat>, +l: Nat, +sp: List<&2, Dr.Span>, +ns: List<&2, Dr.Note>, ih: {DocRows.rows.Marks(sp, raw, Maybe.or(&2, Nat, DocRows.rows.If(Maybe<&2, Nat>, c, None{}, Some{l}), prev)) == True{} : Bool}) -> {DocRows.rows.Marks(gm.fst(DocRows.rows.Pick(List<&2, Dr.Span> & List<&2, Dr.Note>, c, (sp, Dr.RangeBeyond{st, m} <> ns), (Dr.Span{st, l, Bool.and(Maybe.is_some(&2, Nat, prev), Bool.or(raw, Bool.not(Nat.is_eq(Nat.add(Maybe.default(&2, Nat, prev, 0n), 1n), st))))} <> sp, ns))), raw, prev) == True{} : Bool}:
  match c:
    case True{}:
      ih
    case False{}:
      gm.and_t(DocRows.rows.Same(Bool.and(Maybe.is_some(&2, Nat, prev), Bool.or(raw, Bool.not(Nat.is_eq(Nat.add(Maybe.default(&2, Nat, prev, 0n), 1n), st)))), DocRows.rows.Marked(raw, prev, st)), DocRows.rows.Marks(sp, raw, Some{l}), gm.same(raw, prev, st), ih)

def gm.step(+raw: Bool, +prev: Maybe<&2, Nat>, +st: Nat, +m: Maybe<&2, Nat>, +t: Nat, r: List<&2, Dr.Span> & List<&2, Dr.Note>, ih: {DocRows.rows.Marks(gm.fst(r), raw, Maybe.or(&2, Nat, DocRows.rows.Ranges.end(st, m, t), prev)) == True{} : Bool}) -> {DocRows.rows.Marks(gm.fst(DocRows.rows.Ranges.step(raw, prev, st, m, t, r)), raw, prev) == True{} : Bool}:
  match r:
    case (sp, ns):
      gm.step_c(Nat.is_lt(t, st), raw, prev, st, m, Nat.min(Maybe.default(&2, Nat, m, t), t), sp, ns, ih)

# ranges in order, after the span that ended at prev
def gm.rng(xs: List<&2, Dr.Range>, +raw: Bool, +prev: Maybe<&2, Nat>, +t: Nat) -> {DocRows.rows.Marks(gm.fst(DocRows.rows.Ranges(xs, raw, prev, t)), raw, prev) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Dr.Range{+st, +m}:
          gm.step(raw, prev, st, m, t, DocRows.rows.Ranges(rest, raw, Maybe.or(&2, Nat, DocRows.rows.Ranges.end(st, m, t), prev), t), gm.rng(rest, raw, Maybe.or(&2, Nat, DocRows.rows.Ranges.end(st, m, t), prev), t))

def gm.one(+raw: Bool, x: Dr.Range, +t: Nat) -> {DocRows.rows.Marks(gm.fst(DocRows.rows.Window.of(raw, x, t)), raw, None{}) == True{} : Bool}:
  match x:
    case Dr.Range{st, m}:
      gm.win(raw, raw, st, m, t)

# what any selector shows of a file of t lines
def gm.shown(s: Dr.Sel, +t: Nat) -> {DocRows.rows.Marks(gm.fst(DocRows.rows.Shown(s, t)), DocRows.rows.Raw(s), None{}) == True{} : Bool}:
  match s:
    case Dr.Whole{}:
      gm.win(False{}, False{}, 1n, None{}, t)
    case Dr.Raw{}:
      gm.span(True{}, Nat.is_le(1n, t), 1n, t)
    case Dr.Lines{xs, +raw}:
      match xs:
        case Nil{}:
          gm.win(raw, raw, 1n, None{}, t)
        case x <> rest:
          match rest:
            case Nil{}:
              gm.one(raw, x, t)
            case y <> more:
              gm.rng(x <> y <> more, raw, None{}, t)

def gm.spans_fin(t: Nat, raw: Bool, utf8: Bool, over: Bool, r: List<&2, Dr.Span> & List<&2, Dr.Note>) -> {DocRows.rows.Spans(DocRows.rows.View.fin(t, raw, utf8, over, r)) == gm.fst(r) : List<&2, Dr.Span>}:
  match r:
    case (sp, ns):
      {==}

def gm.view(+s: Dr.Sel, +utf8: Bool, +over: Bool, +ls: List<&2, Dl.Line>) -> {DocRows.rows.Marks(DocRows.rows.Spans(DocRows.rows.View(s, utf8, over, ls)), DocRows.rows.Raw(s), None{}) == True{} : Bool}:
  +t = DocRows.rows.If(Nat, DocRows.rows.Raw(s), List.length(&2, Dl.Line, ls), DocRows.rows.Count(ls))
  %Equal.sym(List<&2, Dr.Span>, DocRows.rows.Spans(DocRows.rows.View.fin(t, DocRows.rows.Raw(s), utf8, over, DocRows.rows.Shown(s, t))), gm.fst(DocRows.rows.Shown(s, t)), gm.spans_fin(t, DocRows.rows.Raw(s), utf8, over, DocRows.rows.Shown(s, t))) : {DocRows.rows.Marks(_, DocRows.rows.Raw(s), None{}) == True{} : Bool}
  gm.shown(s, t)

def DocRows.rows_gap_marks_every_jump(s, utf8, over, p):
  match p:
    case Dl.Proj{+b, +ls}:
      %Equal.sym(Dr.View, Dr.view(s, utf8, over, Dl.Proj{b, ls}), DocRows.rows.View(s, utf8, over, ls), DocRows.rows_view_shows(s, utf8, over, b, ls)) : {DocRows.rows.Marks(DocRows.rows.Spans(_), DocRows.rows.Raw(s), None{}) == True{} : Bool}
      gm.view(s, utf8, over, ls)
