# eukhe: LAW rows_view_shows, ranges (two or more)

import Base
import ../../../bend/doc_rows.bend as Dr
import ../../../laws/doc_rows.bend as DocRows
import ../base.bend as DRB

# a range cut at the end of the file ends at the rule's end
def rvs.cut(m: Maybe<&2, Nat>, +t: Nat) -> {Dr.ranges.cut(m, t) == Nat.min(Maybe.default(&2, Nat, m, t), t) : Nat}:
  match m:
    case None{}:
      Equal.sym(Nat, Nat.min(t, t), t, DRB.drb.min_self(t))
    case Some{+k}:
      Equal.sym(Nat, Nat.min(k, t), Dr.low(k, t), DRB.drb.min_pick(k, t))

# the gap marker before a span is the rule's: before every span but the
# first that does not start right after the span before (raw: every one)
def rvs.gap(prev: Maybe<&2, Nat>, raw: Bool, +st: Nat) -> {Dr.ranges.gap(prev, raw, st) == Bool.and(Maybe.is_some(&2, Nat, prev), Bool.or(raw, Bool.not(Nat.is_eq(Nat.add(Maybe.default(&2, Nat, prev, 0n), 1n), st)))) : Bool}:
  match prev:
    case None{}:
      {==}
    case Some{+pe}:
      match raw:
        case True{}:
          {==}
        case False{}:
          %Equal.sym(Nat, Nat.add(pe, 1n), 1n+pe, DRB.drb.add_one(pe)) : {Bool.not(Nat.is_eq(1n+pe, st)) == Bool.not(Nat.is_eq(_, st)) : Bool}
          {==}

# the end of the last span shown, threaded on: the rule's
def rvs.prev(c: Bool, prev: Maybe<&2, Nat>, +l: Nat) -> {Bool.pick(Maybe<&2, Nat>, c, prev, Some{l}) == Maybe.or(&2, Nat, DocRows.rows.If(Maybe<&2, Nat>, c, None{}, Some{l}), prev) : Maybe<&2, Nat>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# a range put before the rest: its notice, or its span
def rvs.put(c: Bool, +st: Nat, +m: Maybe<&2, Nat>, +l: Nat, +g: Bool, +sp: List<&2, Dr.Span>, +ns: List<&2, Dr.Note>) -> {Dr.ranges.put(c, st, m, l, g, (sp, ns)) == DocRows.rows.Pick(List<&2, Dr.Span> & List<&2, Dr.Note>, c, (sp, Dr.RangeBeyond{st, m} <> ns), (Dr.Span{st, l, g} <> sp, ns)) : List<&2, Dr.Span> & List<&2, Dr.Note>}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# one range step before any rest
def rvs.step(+raw: Bool, +prev: Maybe<&2, Nat>, +st: Nat, +m: Maybe<&2, Nat>, +t: Nat, r: List<&2, Dr.Span> & List<&2, Dr.Note>) -> {Dr.ranges.put(Nat.is_lt(t, st), st, m, Nat.min(Maybe.default(&2, Nat, m, t), t), Bool.and(Maybe.is_some(&2, Nat, prev), Bool.or(raw, Bool.not(Nat.is_eq(Nat.add(Maybe.default(&2, Nat, prev, 0n), 1n), st)))), r) == DocRows.rows.Ranges.step(raw, prev, st, m, t, r) : List<&2, Dr.Span> & List<&2, Dr.Note>}:
  match r:
    case (sp, ns):
      rvs.put(Nat.is_lt(t, st), st, m, Nat.min(Maybe.default(&2, Nat, m, t), t), Bool.and(Maybe.is_some(&2, Nat, prev), Bool.or(raw, Bool.not(Nat.is_eq(Nat.add(Maybe.default(&2, Nat, prev, 0n), 1n), st)))), sp, ns)

# ranges in order, after the span that ended at prev: the rule's
def rvs.rng(xs: List<&2, Dr.Range>, +raw: Bool, +prev: Maybe<&2, Nat>, +t: Nat) -> {Dr.ranges.go(xs, raw, prev, t) == DocRows.rows.Ranges(xs, raw, prev, t) : List<&2, Dr.Span> & List<&2, Dr.Note>}:
  match xs:
    case Nil{}:
      {==}
    case x <> +rest:
      match x:
        case Dr.Range{+st, +m}:
          %Equal.sym(Nat, Dr.ranges.cut(m, t), Nat.min(Maybe.default(&2, Nat, m, t), t), rvs.cut(m, t)) : {Dr.ranges.put(Nat.is_lt(t, st), st, m, _, Dr.ranges.gap(prev, raw, st), Dr.ranges.go(rest, raw, Bool.pick(Maybe<&2, Nat>, Nat.is_lt(t, st), prev, Some{_}), t)) == DocRows.rows.Ranges(Dr.Range{st, m} <> rest, raw, prev, t) : List<&2, Dr.Span> & List<&2, Dr.Note>}
          %Equal.sym(List<&2, Dr.Span> & List<&2, Dr.Note>, Dr.ranges.go(rest, raw, Bool.pick(Maybe<&2, Nat>, Nat.is_lt(t, st), prev, Some{Nat.min(Maybe.default(&2, Nat, m, t), t)}), t), DocRows.rows.Ranges(rest, raw, Bool.pick(Maybe<&2, Nat>, Nat.is_lt(t, st), prev, Some{Nat.min(Maybe.default(&2, Nat, m, t), t)}), t), rvs.rng(rest, raw, Bool.pick(Maybe<&2, Nat>, Nat.is_lt(t, st), prev, Some{Nat.min(Maybe.default(&2, Nat, m, t), t)}), t)) : {Dr.ranges.put(Nat.is_lt(t, st), st, m, Nat.min(Maybe.default(&2, Nat, m, t), t), Dr.ranges.gap(prev, raw, st), _) == DocRows.rows.Ranges(Dr.Range{st, m} <> rest, raw, prev, t) : List<&2, Dr.Span> & List<&2, Dr.Note>}
          %Equal.sym(Maybe<&2, Nat>, Bool.pick(Maybe<&2, Nat>, Nat.is_lt(t, st), prev, Some{Nat.min(Maybe.default(&2, Nat, m, t), t)}), Maybe.or(&2, Nat, DocRows.rows.If(Maybe<&2, Nat>, Nat.is_lt(t, st), None{}, Some{Nat.min(Maybe.default(&2, Nat, m, t), t)}), prev), rvs.prev(Nat.is_lt(t, st), prev, Nat.min(Maybe.default(&2, Nat, m, t), t))) : {Dr.ranges.put(Nat.is_lt(t, st), st, m, Nat.min(Maybe.default(&2, Nat, m, t), t), Dr.ranges.gap(prev, raw, st), DocRows.rows.Ranges(rest, raw, _, t)) == DocRows.rows.Ranges(Dr.Range{st, m} <> rest, raw, prev, t) : List<&2, Dr.Span> & List<&2, Dr.Note>}
          %Equal.sym(Bool, Dr.ranges.gap(prev, raw, st), Bool.and(Maybe.is_some(&2, Nat, prev), Bool.or(raw, Bool.not(Nat.is_eq(Nat.add(Maybe.default(&2, Nat, prev, 0n), 1n), st)))), rvs.gap(prev, raw, st)) : {Dr.ranges.put(Nat.is_lt(t, st), st, m, Nat.min(Maybe.default(&2, Nat, m, t), t), _, DocRows.rows.Ranges(rest, raw, Maybe.or(&2, Nat, DocRows.rows.If(Maybe<&2, Nat>, Nat.is_lt(t, st), None{}, Some{Nat.min(Maybe.default(&2, Nat, m, t), t)}), prev), t)) == DocRows.rows.Ranges(Dr.Range{st, m} <> rest, raw, prev, t) : List<&2, Dr.Span> & List<&2, Dr.Note>}
          rvs.step(raw, prev, st, m, t, DocRows.rows.Ranges(rest, raw, Maybe.or(&2, Nat, DocRows.rows.If(Maybe<&2, Nat>, Nat.is_lt(t, st), None{}, Some{Nat.min(Maybe.default(&2, Nat, m, t), t)}), prev), t))
