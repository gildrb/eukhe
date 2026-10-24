# eukhe: LAW rows_view_shows, a window (no selector or one range)

import Base
import ../../../bend/doc_rows.bend as Dr
import ../../../laws/doc_rows.bend as DocRows
import ../base.bend as DRB

# a span under a flag is the rule's span under it
def rvs.span_if(ok: Bool, +s: Nat, +e: Nat) -> {Dr.span.if(ok, s, e) == DocRows.rows.If(List<&2, Dr.Span>, ok, [Dr.Span{s, e, False{}}], Nil{}) : List<&2, Dr.Span>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

# lines s..e: the rule's span
def rvs.span_of(+s: Nat, +e: Nat) -> {Dr.span.of(s, e) == DocRows.rows.Span(s, e) : List<&2, Dr.Span>}:
  rvs.span_if(Nat.is_le(s, e), s, e)

# the notice of the lines that remain after line e
def rvs.left(c: Bool, +e: Nat, +t: Nat) -> {Dr.window.left(c, e, t) == DocRows.rows.If(List<&2, Dr.Note>, c, [Dr.Remain{Nat.sub(t, e), Nat.add(e, 1n)}], Nil{}) : List<&2, Dr.Note>}:
  match c:
    case True{}:
      %Equal.sym(Nat, Nat.add(e, 1n), 1n+e, DRB.drb.add_one(e)) : {[Dr.Remain{Nat.sub(t, e), 1n+e}] == [Dr.Remain{Nat.sub(t, e), _}] : List<&2, Dr.Note>}
      {==}
    case False{}:
      {==}

# the first line shown, from 0 plus one, is the rule's first line from 1
def rvs.first(raw: Bool, +rs: Nat) -> {1n+Bool.pick(Nat, Bool.and(Bool.not(raw), Nat.is_lt(0n, rs)), Nat.sub(rs, Dr.lead()), rs) == DocRows.rows.Window.first(raw, 1n+rs) : Nat}:
  match raw:
    case True{}:
      {==}
    case False{}:
      match rs:
        case 0n:
          {==}
        case 1n+j:
          %Equal.sym(Nat, Nat.sub(j, 0n), j, DRB.drb.sub_zero(j)) : {1n+_ == 1n+j : Nat}
          {==}

# a window with no end: from its first line to the end of the file
def rvs.show_none(raw: Bool, +rs: Nat, +t: Nat) -> {Dr.window.show(raw, rs, t, False{}, t) == (DocRows.rows.Span(DocRows.rows.Window.first(raw, 1n+rs), t), Nil{}) : List<&2, Dr.Span> & List<&2, Dr.Note>}:
  match raw:
    case True{}:
      %Equal.sym(List<&2, Dr.Span>, Dr.span.of(1n+rs, t), DocRows.rows.Span(1n+rs, t), rvs.span_of(1n+rs, t)) : {(_, Nil{}) == (DocRows.rows.Span(1n+rs, t), Nil{}) : List<&2, Dr.Span> & List<&2, Dr.Note>}
      {==}
    case False{}:
      %Equal.sym(List<&2, Dr.Span>, Dr.span.of(1n+Bool.pick(Nat, Nat.is_lt(0n, rs), Nat.sub(rs, Dr.lead()), rs), t), DocRows.rows.Span(1n+Bool.pick(Nat, Nat.is_lt(0n, rs), Nat.sub(rs, Dr.lead()), rs), t), rvs.span_of(1n+Bool.pick(Nat, Nat.is_lt(0n, rs), Nat.sub(rs, Dr.lead()), rs), t)) : {(_, Nil{}) == (DocRows.rows.Span(DocRows.rows.Window.first(False{}, 1n+rs), t), Nil{}) : List<&2, Dr.Span> & List<&2, Dr.Note>}
      %Equal.sym(Nat, 1n+Bool.pick(Nat, Bool.and(Bool.not(False{}), Nat.is_lt(0n, rs)), Nat.sub(rs, Dr.lead()), rs), DocRows.rows.Window.first(False{}, 1n+rs), rvs.first(False{}, rs)) : {(DocRows.rows.Span(_, t), Nil{}) == (DocRows.rows.Span(DocRows.rows.Window.first(False{}, 1n+rs), t), Nil{}) : List<&2, Dr.Span> & List<&2, Dr.Note>}
      {==}

# a window that ends at line w (raw: no context, no notice)
def rvs.ends(raw: Bool, +rs: Nat, +w: Nat, +t: Nat) -> {Dr.window.show(raw, rs, w, True{}, t) == DocRows.rows.Window.ends(raw, DocRows.rows.Window.first(raw, 1n+rs), w, t) : List<&2, Dr.Span> & List<&2, Dr.Note>}:
  match raw:
    case True{}:
      %Equal.sym(List<&2, Dr.Span>, Dr.span.of(1n+rs, w), DocRows.rows.Span(1n+rs, w), rvs.span_of(1n+rs, w)) : {(_, Nil{}) == (DocRows.rows.Span(1n+rs, w), Nil{}) : List<&2, Dr.Span> & List<&2, Dr.Note>}
      {==}
    case False{}:
      %DRB.drb.min_pick(Nat.add(w, 3n), t) : {(Dr.span.of(1n+Bool.pick(Nat, Nat.is_lt(0n, rs), Nat.sub(rs, Dr.lead()), rs), _), Dr.window.remain(True{}, _, t)) == DocRows.rows.Window.ends(False{}, DocRows.rows.Window.first(False{}, 1n+rs), w, t) : List<&2, Dr.Span> & List<&2, Dr.Note>}
      %Equal.sym(List<&2, Dr.Span>, Dr.span.of(1n+Bool.pick(Nat, Nat.is_lt(0n, rs), Nat.sub(rs, Dr.lead()), rs), Nat.min(Nat.add(w, 3n), t)), DocRows.rows.Span(1n+Bool.pick(Nat, Nat.is_lt(0n, rs), Nat.sub(rs, Dr.lead()), rs), Nat.min(Nat.add(w, 3n), t)), rvs.span_of(1n+Bool.pick(Nat, Nat.is_lt(0n, rs), Nat.sub(rs, Dr.lead()), rs), Nat.min(Nat.add(w, 3n), t))) : {(_, Dr.window.remain(True{}, Nat.min(Nat.add(w, 3n), t), t)) == DocRows.rows.Window.ends(False{}, DocRows.rows.Window.first(False{}, 1n+rs), w, t) : List<&2, Dr.Span> & List<&2, Dr.Note>}
      %Equal.sym(List<&2, Dr.Note>, Dr.window.left(Nat.is_lt(Nat.min(Nat.add(w, 3n), t), t), Nat.min(Nat.add(w, 3n), t), t), DocRows.rows.If(List<&2, Dr.Note>, Nat.is_lt(Nat.min(Nat.add(w, 3n), t), t), [Dr.Remain{Nat.sub(t, Nat.min(Nat.add(w, 3n), t)), Nat.add(Nat.min(Nat.add(w, 3n), t), 1n)}], Nil{}), rvs.left(Nat.is_lt(Nat.min(Nat.add(w, 3n), t), t), Nat.min(Nat.add(w, 3n), t), t)) : {(DocRows.rows.Span(1n+Bool.pick(Nat, Nat.is_lt(0n, rs), Nat.sub(rs, Dr.lead()), rs), Nat.min(Nat.add(w, 3n), t)), _) == DocRows.rows.Window.ends(False{}, DocRows.rows.Window.first(False{}, 1n+rs), w, t) : List<&2, Dr.Span> & List<&2, Dr.Note>}
      %Equal.sym(Nat, 1n+Bool.pick(Nat, Bool.and(Bool.not(False{}), Nat.is_lt(0n, rs)), Nat.sub(rs, Dr.lead()), rs), DocRows.rows.Window.first(False{}, 1n+rs), rvs.first(False{}, rs)) : {(DocRows.rows.Span(_, Nat.min(Nat.add(w, 3n), t)), DocRows.rows.If(List<&2, Dr.Note>, Nat.is_lt(Nat.min(Nat.add(w, 3n), t), t), [Dr.Remain{Nat.sub(t, Nat.min(Nat.add(w, 3n), t)), Nat.add(Nat.min(Nat.add(w, 3n), t), 1n)}], Nil{})) == DocRows.rows.Window.ends(False{}, DocRows.rows.Window.first(False{}, 1n+rs), w, t) : List<&2, Dr.Span> & List<&2, Dr.Note>}
      {==}

# a window that starts at line rs + 1 of a file of t lines (c: it starts in the file)
def rvs.in(c: Bool, m: Maybe<&2, Nat>, +raw: Bool, +rs: Nat, +st: Nat, +t: Nat) -> {Dr.window.in(c, raw, rs, st, m, t) == DocRows.rows.Pick(List<&2, Dr.Span> & List<&2, Dr.Note>, Bool.not(c), (Nil{}, [Dr.Beyond{1n+rs}]), DocRows.rows.Window.in(raw, 1n+rs, m, st, t)) : List<&2, Dr.Span> & List<&2, Dr.Note>}:
  match c:
    case False{}:
      {==}
    case True{}:
      match m:
        case None{}:
          rvs.show_none(raw, rs, t)
        case Some{+en}:
          %DRB.drb.min_pick(Nat.add(rs, 1n+Nat.sub(en, st)), t) : {Dr.window.show(raw, rs, _, True{}, t) == DocRows.rows.Window.in(raw, 1n+rs, Some{en}, st, t) : List<&2, Dr.Span> & List<&2, Dr.Note>}
          %Equal.sym(Nat, Nat.add(rs, 1n+Nat.sub(en, st)), 1n+Nat.add(rs, Nat.sub(en, st)), DRB.drb.add_succ(rs, Nat.sub(en, st))) : {Dr.window.show(raw, rs, Nat.min(_, t), True{}, t) == DocRows.rows.Window.in(raw, 1n+rs, Some{en}, st, t) : List<&2, Dr.Span> & List<&2, Dr.Note>}
          rvs.ends(raw, rs, Nat.min(1n+Nat.add(rs, Nat.sub(en, st)), t), t)

# the window from line rs + 1: it starts past the end exactly when t < rs + 1
def rvs.at_rs(+raw: Bool, +rs: Nat, +st: Nat, +m: Maybe<&2, Nat>, +t: Nat) -> {Dr.window.in(Nat.is_lt(rs, t), raw, rs, st, m, t) == DocRows.rows.Pick(List<&2, Dr.Span> & List<&2, Dr.Note>, Nat.is_lt(t, 1n+rs), (Nil{}, [Dr.Beyond{1n+rs}]), DocRows.rows.Window.in(raw, 1n+rs, m, st, t)) : List<&2, Dr.Span> & List<&2, Dr.Note>}:
  %Equal.sym(Bool, Nat.is_lt(t, 1n+rs), Bool.not(Nat.is_lt(rs, t)), DRB.drb.lt_flip(rs, t)) : {Dr.window.in(Nat.is_lt(rs, t), raw, rs, st, m, t) == DocRows.rows.Pick(List<&2, Dr.Span> & List<&2, Dr.Note>, _, (Nil{}, [Dr.Beyond{1n+rs}]), DocRows.rows.Window.in(raw, 1n+rs, m, st, t)) : List<&2, Dr.Span> & List<&2, Dr.Note>}
  rvs.in(Nat.is_lt(rs, t), m, raw, rs, st, t)

# a window from line st: 0-based st - 1 is 1-based max(st, 1)
def rvs.at(+st: Nat, +raw: Bool, +m: Maybe<&2, Nat>, +t: Nat) -> {Dr.window.at(raw, st, m, t) == DocRows.rows.Window(raw, st, m, t) : List<&2, Dr.Span> & List<&2, Dr.Note>}:
  match st:
    case 0n:
      rvs.at_rs(raw, 0n, 0n, m, t)
    case 1n+k:
      match k:
        case 0n:
          rvs.at_rs(raw, 0n, 1n, m, t)
        case 1n+j:
          rvs.at_rs(raw, 1n+j, 1n+1n+j, m, t)
