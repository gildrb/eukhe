# eukhe: lemmas of the proof of LAW sel_release_copies: one row
#
# The spec picks a row's glyphs by comparing cells (sl_pick); the model
# reads the row as a range of glyph indexes: from the first glyph that
# reaches the first column (M.row_lo) to past the last one that starts at
# or before the last column and counts (M.row_nb). src.colf is the spec's
# pick read by columns: on a row strictly inside the range every glyph
# passes, the first row bounds the start, the last row the end
# (src.pick). Columns grow along a row, so a glyph past the end leaves no
# later glyph in (src.colf_out, src.nb_out), and after the first glyph
# that reaches the start every later one does (src.lo_at, src.colf_from).
# src.range: the tokens of the picked glyphs, the trailing blanks dropped
# when trim, are the span of the model's range.

import Base
import ../../../bend/selection.bend as M
import ../../../laws/selection.bend as Selection
import ../base.bend as LS

# The column filter
# -----------------

# glyphs from column c and index j on that start at or before `to` and
# reach `from`
def src.colf(gs: List<&2, Nat>, +c: Nat, +j: Nat, +from: Maybe<&2, Nat>, +to: Maybe<&2, Nat>) -> List<&2, Selection.SlGl>:
  match gs:
    case Nil{}:
      Nil{}
    case Con{+g, rest}:
      Selection.sl_pick.k(Bool.and(M.before(c, to), M.reach(from, g, c)), Selection.SlGl{j, g}, src.colf(rest, M.gnext(g, c), 1n+j, from, to))

# a glyph reaches `from` when its last cell is at or past it
def src.reachL(from: Maybe<&2, Nat>, L: Nat) -> Bool:
  match from:
    case None{}:
      True{}
    case Some{f}:
      Nat.is_le(f, L)

def src.reach_eq(from: Maybe<&2, Nat>, g: Nat, +c: Nat) -> {M.reach(from, g, c) == src.reachL(from, Selection.sl_last(g, c)) : Bool}:
  match from:
    case None{}:
      {==}
    case Some{f}:
      match g:
        case 0n:
          {==}
        case 1n+p:
          {==}

def src.next_eq(g: Nat, +c: Nat) -> {M.gnext(g, c) == Selection.sl_next(g, c) : Nat}:
  match g:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a glyph starts at or after column c, and its last cell too
def src.c_le_last(g: Nat, +c: Nat) -> {Nat.is_le(c, M.glast(g, c)) == True{} : Bool}:
  match g:
    case 0n:
      LS.ls.le_refl(c)
    case 1n+p:
      LS.ls.le_add(p, c)

def src.c_le_next(+g: Nat, +c: Nat) -> {Nat.is_le(c, M.gnext(g, c)) == True{} : Bool}:
  LS.ls.le_trans(c, M.glast(g, c), 1n+M.glast(g, c), src.c_le_last(g, c), LS.ls.le_succ(M.glast(g, c)))

# The row's bounds from its row id
# --------------------------------

def src.tof(qb1: Bool, qb2: Bool, c2: Nat) -> Maybe<&2, Nat>:
  match qb1:
    case True{}:
      None{}
    case False{}:
      Some{c2}

def src.fromf(qa1: Bool, qa2: Bool, c1: Nat) -> Maybe<&2, Nat>:
  match qa1:
    case True{}:
      None{}
    case False{}:
      Some{c1}

def src.pw.b(qb1: Bool, qb2: Bool, -B1: Bool, -B2: Bool, +c: Nat, +c2: Nat, eb1: {B1 == qb1 : Bool}, eb2: {B2 == qb2 : Bool}, hb: {Bool.or(qb1, qb2) == True{} : Bool}) -> {Bool.or(B1, Bool.and(B2, Nat.is_le(c, c2))) == M.before(c, src.tof(qb1, qb2, c2)) : Bool}:
  match qb1:
    case True{}:
      %Equal.sym(Bool, B1, True{}, eb1) : {Bool.or(_, Bool.and(B2, Nat.is_le(c, c2))) == True{} : Bool}
      {==}
    case False{}:
      match qb2:
        case True{}:
          %Equal.sym(Bool, B1, False{}, eb1) : {Bool.or(_, Bool.and(B2, Nat.is_le(c, c2))) == Nat.is_le(c, c2) : Bool}
          %Equal.sym(Bool, B2, True{}, eb2) : {Bool.and(_, Nat.is_le(c, c2)) == Nat.is_le(c, c2) : Bool}
          {==}
        case False{}:
          LS.ls.absurd({Bool.or(B1, Bool.and(B2, Nat.is_le(c, c2))) == Nat.is_le(c, c2) : Bool}, hb)

def src.pw.a(qa1: Bool, qa2: Bool, -A1: Bool, -A2: Bool, +c1: Nat, +L: Nat, ea1: {A1 == qa1 : Bool}, ea2: {A2 == qa2 : Bool}, ha: {Bool.or(qa1, qa2) == True{} : Bool}) -> {Bool.or(A1, Bool.and(A2, Nat.is_le(c1, L))) == src.reachL(src.fromf(qa1, qa2, c1), L) : Bool}:
  match qa1:
    case True{}:
      %Equal.sym(Bool, A1, True{}, ea1) : {Bool.or(_, Bool.and(A2, Nat.is_le(c1, L))) == True{} : Bool}
      {==}
    case False{}:
      match qa2:
        case True{}:
          %Equal.sym(Bool, A1, False{}, ea1) : {Bool.or(_, Bool.and(A2, Nat.is_le(c1, L))) == Nat.is_le(c1, L) : Bool}
          %Equal.sym(Bool, A2, True{}, ea2) : {Bool.and(_, Nat.is_le(c1, L)) == Nat.is_le(c1, L) : Bool}
          {==}
        case False{}:
          LS.ls.absurd({Bool.or(A1, Bool.and(A2, Nat.is_le(c1, L))) == Nat.is_le(c1, L) : Bool}, ha)

# the spec's pick of row R, a row in the range, is the column filter of
# its bounds
def src.pick(gs: List<&2, Nat>, +c: Nat, +j: Nat, +R: Nat, +r1: Nat, +c1: Nat, +r2: Nat, +c2: Nat, +qb1: Bool, +qb2: Bool, +qa1: Bool, +qa2: Bool, +eb1: {Nat.is_lt(R, r2) == qb1 : Bool}, +eb2: {Nat.is_eq(R, r2) == qb2 : Bool}, +ea1: {Nat.is_lt(r1, R) == qa1 : Bool}, +ea2: {Nat.is_eq(r1, R) == qa2 : Bool}, +hb: {Bool.or(qb1, qb2) == True{} : Bool}, +ha: {Bool.or(qa1, qa2) == True{} : Bool}) -> {Selection.sl_pick(gs, c, j, R, M.Cell{r1, c1}, M.Cell{r2, c2}) == src.colf(gs, c, j, src.fromf(qa1, qa2, c1), src.tof(qb1, qb2, c2)) : List<&2, Selection.SlGl>}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      +FROM = src.fromf(qa1, qa2, c1)
      +TO = src.tof(qb1, qb2, c2)
      +A = Bool.or(Nat.is_lt(r1, R), Bool.and(Nat.is_eq(r1, R), Nat.is_le(c1, Selection.sl_last(g, c))))
      +TAIL = Selection.sl_pick(rest, Selection.sl_next(g, c), 1n+j, R, M.Cell{r1, c1}, M.Cell{r2, c2})
      +RHS = Selection.sl_pick.k(Bool.and(M.before(c, TO), M.reach(FROM, g, c)), Selection.SlGl{j, g}, src.colf(rest, M.gnext(g, c), 1n+j, FROM, TO))
      %Equal.sym(Bool, Bool.or(Nat.is_lt(R, r2), Bool.and(Nat.is_eq(R, r2), Nat.is_le(c, c2))), M.before(c, TO), src.pw.b(qb1, qb2, Nat.is_lt(R, r2), Nat.is_eq(R, r2), c, c2, eb1, eb2, hb)) : {Selection.sl_pick.k(Bool.and(_, A), Selection.SlGl{j, g}, TAIL) == RHS : List<&2, Selection.SlGl>}
      %Equal.sym(Bool, A, src.reachL(FROM, Selection.sl_last(g, c)), src.pw.a(qa1, qa2, Nat.is_lt(r1, R), Nat.is_eq(r1, R), c1, Selection.sl_last(g, c), ea1, ea2, ha)) : {Selection.sl_pick.k(Bool.and(M.before(c, TO), _), Selection.SlGl{j, g}, TAIL) == RHS : List<&2, Selection.SlGl>}
      %src.reach_eq(FROM, g, c) : {Selection.sl_pick.k(Bool.and(M.before(c, TO), _), Selection.SlGl{j, g}, TAIL) == RHS : List<&2, Selection.SlGl>}
      %Equal.sym(List<&2, Selection.SlGl>, TAIL, src.colf(rest, Selection.sl_next(g, c), 1n+j, FROM, TO), src.pick(rest, Selection.sl_next(g, c), 1n+j, R, r1, c1, r2, c2, qb1, qb2, qa1, qa2, eb1, eb2, ea1, ea2, hb, ha)) : {Selection.sl_pick.k(Bool.and(M.before(c, TO), M.reach(FROM, g, c)), Selection.SlGl{j, g}, _) == RHS : List<&2, Selection.SlGl>}
      %src.next_eq(g, c) : {Selection.sl_pick.k(Bool.and(M.before(c, TO), M.reach(FROM, g, c)), Selection.SlGl{j, g}, src.colf(rest, _, 1n+j, FROM, TO)) == RHS : List<&2, Selection.SlGl>}
      {==}

# Monotone columns
# ----------------

def src.out.k(b: Bool, +c: Nat, +c2: Nat, +t: Nat, eb: {Nat.is_le(c2, t) == b : Bool}, h: {Nat.is_le(c, t) == False{} : Bool}, le: {Nat.is_le(c, c2) == True{} : Bool}) -> {Nat.is_le(c2, t) == False{} : Bool}:
  match b:
    case True{}:
      LS.ls.absurd_t({Nat.is_le(c2, t) == False{} : Bool}, Equal.trans(Bool, True{}, Nat.is_le(c, t), False{}, Equal.sym(Bool, Nat.is_le(c, t), True{}, LS.ls.le_trans(c, c2, t, le, eb)), h))
    case False{}:
      eb

# past `to` at c, past it at any later column
def src.before_mono(+c: Nat, +c2: Nat, to: Maybe<&2, Nat>, h: {M.before(c, to) == False{} : Bool}, le: {Nat.is_le(c, c2) == True{} : Bool}) -> {M.before(c2, to) == False{} : Bool}:
  match to:
    case None{}:
      LS.ls.absurd_t({True{} == False{} : Bool}, h)
    case Some{+t}:
      src.out.k(Nat.is_le(c2, t), c, c2, t, {==}, h, le)

def src.colf_out(gs: List<&2, Nat>, +c: Nat, +j: Nat, +from: Maybe<&2, Nat>, +to: Maybe<&2, Nat>, +h: {M.before(c, to) == False{} : Bool}) -> {src.colf(gs, c, j, from, to) == Nil{} : List<&2, Selection.SlGl>}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      %Equal.sym(Bool, M.before(c, to), False{}, h) : {Selection.sl_pick.k(Bool.and(_, M.reach(from, g, c)), Selection.SlGl{j, g}, src.colf(rest, M.gnext(g, c), 1n+j, from, to)) == Nil{} : List<&2, Selection.SlGl>}
      src.colf_out(rest, M.gnext(g, c), 1n+j, from, to, src.before_mono(c, M.gnext(g, c), to, h, src.c_le_next(g, c)))

def src.nb_out(gs: List<&2, Nat>, +c: Nat, +j: Nat, +to: Maybe<&2, Nat>, +t: Bool, +h: {M.before(c, to) == False{} : Bool}) -> {M.row_nb(gs, c, j, to, t) == 0n : Nat}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      %Equal.sym(Nat, M.row_nb(rest, M.gnext(g, c), 1n+j, to, t), 0n, src.nb_out(rest, M.gnext(g, c), 1n+j, to, t, src.before_mono(c, M.gnext(g, c), to, h, src.c_le_next(g, c)))) : {M.nb.pick(_, Bool.and(M.before(c, to), M.counts(t, g)), j) == 0n : Nat}
      %Equal.sym(Bool, M.before(c, to), False{}, h) : {M.nb.pick(0n, Bool.and(_, M.counts(t, g)), j) == 0n : Nat}
      {==}

# a glyph past column f reaches it
def src.reach_past(from: Maybe<&2, Nat>, +g: Nat, +c: Nat, h: {src.reachL(from, c) == True{} : Bool}) -> {M.reach(from, g, c) == True{} : Bool}:
  match from:
    case None{}:
      {==}
    case Some{+f}:
      LS.ls.le_trans(f, c, M.glast(g, c), h, src.c_le_last(g, c))

# a glyph that reaches column f leaves every later column past f
def src.reach_next(from: Maybe<&2, Nat>, +g: Nat, +c: Nat, h: {M.reach(from, g, c) == True{} : Bool}) -> {src.reachL(from, M.gnext(g, c)) == True{} : Bool}:
  match from:
    case None{}:
      {==}
    case Some{+f}:
      LS.ls.le_trans(f, M.glast(g, c), 1n+M.glast(g, c), h, LS.ls.le_succ(M.glast(g, c)))

def src.reach_mono(from: Maybe<&2, Nat>, +g: Nat, +c: Nat, h: {src.reachL(from, c) == True{} : Bool}) -> {src.reachL(from, M.gnext(g, c)) == True{} : Bool}:
  match from:
    case None{}:
      {==}
    case Some{+f}:
      LS.ls.le_trans(f, c, M.gnext(g, c), h, src.c_le_next(g, c))

# once past `from`, the first glyph is the first that reaches it
def src.lo_at(gs: List<&2, Nat>, +c: Nat, +j: Nat, +from: Maybe<&2, Nat>, h: {src.reachL(from, c) == True{} : Bool}) -> {M.row_lo(gs, c, j, from) == j : Nat}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      %Equal.sym(Bool, M.reach(from, g, c), True{}, src.reach_past(from, g, c, h)) : {M.lo.pick(_, j, M.row_lo(rest, M.gnext(g, c), 1n+j, from)) == j : Nat}
      {==}

def src.lo_ge.k(b: Bool, +j: Nat, +L: Nat, ih: {Nat.is_le(1n+j, L) == True{} : Bool}) -> {Nat.is_le(j, M.lo.pick(b, j, L)) == True{} : Bool}:
  match b:
    case True{}:
      LS.ls.le_refl(j)
    case False{}:
      LS.ls.le_trans(j, 1n+j, L, LS.ls.le_succ(j), ih)

def src.lo_ge(gs: List<&2, Nat>, +c: Nat, +j: Nat, +from: Maybe<&2, Nat>) -> {Nat.is_le(j, M.row_lo(gs, c, j, from)) == True{} : Bool}:
  match gs:
    case Nil{}:
      LS.ls.le_refl(j)
    case Con{+g, +rest}:
      src.lo_ge.k(M.reach(from, g, c), j, M.row_lo(rest, M.gnext(g, c), 1n+j, from), src.lo_ge(rest, M.gnext(g, c), 1n+j, from))

def src.nbok.k(n: Nat, here: Bool, +j: Nat, ih: {LS.ls.nbok(n, 1n+j) == True{} : Bool}) -> {LS.ls.nbok(M.nb.pick(n, here, j), j) == True{} : Bool}:
  match n:
    case 0n:
      match here:
        case True{}:
          LS.ls.le_refl(j)
        case False{}:
          {==}
    case 1n+p:
      LS.ls.le_trans(j, 1n+j, p, LS.ls.le_succ(j), ih)

def src.nbok(gs: List<&2, Nat>, +c: Nat, +j: Nat, +to: Maybe<&2, Nat>, +t: Bool) -> {LS.ls.nbok(M.row_nb(gs, c, j, to, t), j) == True{} : Bool}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      src.nbok.k(M.row_nb(rest, M.gnext(g, c), 1n+j, to, t), Bool.and(M.before(c, to), M.counts(t, g)), j, src.nbok(rest, M.gnext(g, c), 1n+j, to, t))

# past `from` the filter is the filter with no start
def src.colf_from(gs: List<&2, Nat>, +c: Nat, +j: Nat, +from: Maybe<&2, Nat>, +to: Maybe<&2, Nat>, +h: {src.reachL(from, c) == True{} : Bool}) -> {src.colf(gs, c, j, from, to) == src.colf(gs, c, j, None{}, to) : List<&2, Selection.SlGl>}:
  match gs:
    case Nil{}:
      {==}
    case Con{+g, +rest}:
      %Equal.sym(Bool, M.reach(from, g, c), True{}, src.reach_past(from, g, c, h)) : {Selection.sl_pick.k(Bool.and(M.before(c, to), _), Selection.SlGl{j, g}, src.colf(rest, M.gnext(g, c), 1n+j, from, to)) == src.colf(g <> rest, c, j, None{}, to) : List<&2, Selection.SlGl>}
      %src.colf_from(rest, M.gnext(g, c), 1n+j, from, to, src.reach_mono(from, g, c, h)) : {Selection.sl_pick.k(Bool.and(M.before(c, to), True{}), Selection.SlGl{j, g}, src.colf(rest, M.gnext(g, c), 1n+j, from, to)) == Selection.sl_pick.k(Bool.and(M.before(c, to), True{}), Selection.SlGl{j, g}, _) : List<&2, Selection.SlGl>}
      {==}

# The range
# ---------

# the span the model answers for the range from L, N its count past L
def src.sp(+L: Nat, +N: Nat, +i: Nat) -> List<&2, Selection.SlTok>:
  Selection.sl_span(Nat.sub(M.max.pick(Nat.is_le(L, N), L, N), L), i, L)

def src.sp_zero(+L: Nat, +N: Nat, +i: Nat, h: {Nat.is_le(N, L) == True{} : Bool}) -> {src.sp(L, N, i) == Nil{} : List<&2, Selection.SlTok>}:
  %Equal.sym(Nat, Nat.sub(M.max.pick(Nat.is_le(L, N), L, N), L), 0n, LS.ls.hz(L, N, h)) : {Selection.sl_span(_, i, L) == Nil{} : List<&2, Selection.SlTok>}
  {==}

def src.toks_nil(xs: List<&2, Selection.SlGl>, +i: Nat, e: {Selection.sl_toks(xs, i) == Nil{} : List<&2, Selection.SlTok>}) -> {xs == Nil{} : List<&2, Selection.SlGl>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case Selection.SlGl{k, g}:
          LS.ls.cons_nil({Selection.SlGl{k, g} <> rest == Nil{} : List<&2, Selection.SlGl>}, Selection.SlG{i, k}, Selection.sl_toks(rest, i), e)

# the glyph j, kept, with nothing kept after it
def src.last1(t: Bool, g: Nat, +j: Nat, +i: Nat) -> {Selection.sl_toks(Selection.sl_keep.k(Nil{}, t, Selection.SlGl{j, g}), i) == src.sp(j, M.nb.pick(0n, M.counts(t, g), j), i) : List<&2, Selection.SlTok>}:
  match t:
    case False{}:
      %Equal.sym(Bool, Nat.is_le(j, 1n+j), True{}, LS.ls.le_succ(j)) : {[Selection.SlG{i, j}] == Selection.sl_span(Nat.sub(M.max.pick(_, j, 1n+j), j), i, j) : List<&2, Selection.SlTok>}
      %Equal.sym(Nat, Nat.sub(1n+j, j), 1n+Nat.sub(1n+j, 1n+j), LS.ls.sub_pos(1n+j, j, LS.ls.le_refl(1n+j))) : {[Selection.SlG{i, j}] == Selection.sl_span(_, i, j) : List<&2, Selection.SlTok>}
      %Equal.sym(Nat, Nat.sub(j, j), 0n, LS.ls.sub_self(j)) : {[Selection.SlG{i, j}] == Selection.sl_span(1n+_, i, j) : List<&2, Selection.SlTok>}
      {==}
    case True{}:
      match g:
        case 0n:
          Equal.sym(List<&2, Selection.SlTok>, src.sp(j, 0n, i), Nil{}, src.sp_zero(j, 0n, i, LS.ls.le_zero(j)))
        case 1n+p:
          %Equal.sym(Bool, Nat.is_le(j, 1n+j), True{}, LS.ls.le_succ(j)) : {[Selection.SlG{i, j}] == Selection.sl_span(Nat.sub(M.max.pick(_, j, 1n+j), j), i, j) : List<&2, Selection.SlTok>}
          %Equal.sym(Nat, Nat.sub(1n+j, j), 1n+Nat.sub(1n+j, 1n+j), LS.ls.sub_pos(1n+j, j, LS.ls.le_refl(1n+j))) : {[Selection.SlG{i, j}] == Selection.sl_span(_, i, j) : List<&2, Selection.SlTok>}
          %Equal.sym(Nat, Nat.sub(j, j), 0n, LS.ls.sub_self(j)) : {[Selection.SlG{i, j}] == Selection.sl_span(1n+_, i, j) : List<&2, Selection.SlTok>}
          {==}

# 1 + p less j, j at most p
def src.sub_succ(p: Nat, j: Nat, h: {Nat.is_le(j, p) == True{} : Bool}) -> {Nat.sub(1n+p, j) == 1n+Nat.sub(p, j) : Nat}:
  match p j:
    case q 0n:
      %Equal.sym(Nat, Nat.sub(q, 0n), q, LS.ls.sub_zero(q)) : {1n+q == 1n+_ : Nat}
      {==}
    case 0n 1n+r:
      LS.ls.absurd({Nat.sub(1n, 1n+r) == 1n+Nat.sub(0n, 1n+r) : Nat}, h)
    case 1n+q 1n+r:
      src.sub_succ(q, r, h)

# with j <= p, the model's span from j over 1 + p
def src.rb.sp(+j: Nat, +p: Nat, +i: Nat, jp: {Nat.is_le(j, p) == True{} : Bool}) -> {src.sp(1n+j, 1n+p, i) == Selection.sl_span(Nat.sub(p, j), i, 1n+j) : List<&2, Selection.SlTok>}:
  %Equal.sym(Bool, Nat.is_le(j, p), True{}, jp) : {Selection.sl_span(Nat.sub(M.max.pick(_, 1n+j, 1n+p), 1n+j), i, 1n+j) == Selection.sl_span(Nat.sub(p, j), i, 1n+j) : List<&2, Selection.SlTok>}
  {==}

# with j < p, the span from j + 1 over p - j holds a glyph
def src.span_pos(+p: Nat, +j: Nat, +i: Nat, ok: {Nat.is_le(1n+j, p) == True{} : Bool}) -> {Selection.sl_span(Nat.sub(p, j), i, 1n+j) == Selection.SlG{i, 1n+j} <> Selection.sl_span(Nat.sub(p, 1n+j), i, 2n+j) : List<&2, Selection.SlTok>}:
  %Equal.sym(Nat, Nat.sub(p, j), 1n+Nat.sub(p, 1n+j), LS.ls.sub_pos(p, j, ok)) : {Selection.sl_span(_, i, 1n+j) == Selection.SlG{i, 1n+j} <> Selection.sl_span(Nat.sub(p, 1n+j), i, 2n+j) : List<&2, Selection.SlTok>}
  {==}

def src.rb.cons(ks: List<&2, Selection.SlGl>, t: Bool, +g: Nat, +j: Nat, +i: Nat, +p: Nat, eks: {Selection.sl_toks(ks, i) == Selection.sl_span(Nat.sub(p, j), i, 1n+j) : List<&2, Selection.SlTok>}, +jp: {Nat.is_le(j, p) == True{} : Bool}, +ok: {Nat.is_le(1n+j, p) == True{} : Bool}) -> {Selection.sl_toks(Selection.sl_keep.k(ks, t, Selection.SlGl{j, g}), i) == src.sp(j, 1n+p, i) : List<&2, Selection.SlTok>}:
  match ks:
    case Nil{}:
      LS.ls.cons_nil({Selection.sl_toks(Selection.sl_keep.k(Nil{}, t, Selection.SlGl{j, g}), i) == src.sp(j, 1n+p, i) : List<&2, Selection.SlTok>}, Selection.SlG{i, 1n+j}, Selection.sl_span(Nat.sub(p, 1n+j), i, 2n+j), Equal.sym(List<&2, Selection.SlTok>, Nil{}, Selection.SlG{i, 1n+j} <> Selection.sl_span(Nat.sub(p, 1n+j), i, 2n+j), Equal.trans(List<&2, Selection.SlTok>, Nil{}, Selection.sl_span(Nat.sub(p, j), i, 1n+j), Selection.SlG{i, 1n+j} <> Selection.sl_span(Nat.sub(p, 1n+j), i, 2n+j), eks, src.span_pos(p, j, i, ok))))
    case Con{y, ys}:
      %Equal.sym(Bool, Nat.is_le(j, 1n+p), True{}, LS.ls.le_trans(j, p, 1n+p, jp, LS.ls.le_succ(p))) : {Selection.SlG{i, j} <> Selection.sl_toks(y <> ys, i) == Selection.sl_span(Nat.sub(M.max.pick(_, j, 1n+p), j), i, j) : List<&2, Selection.SlTok>}
      %Equal.sym(Nat, Nat.sub(1n+p, j), 1n+Nat.sub(p, j), src.sub_succ(p, j, jp)) : {Selection.SlG{i, j} <> Selection.sl_toks(y <> ys, i) == Selection.sl_span(_, i, j) : List<&2, Selection.SlTok>}
      %eks : {Selection.SlG{i, j} <> Selection.sl_toks(y <> ys, i) == Selection.SlG{i, j} <> _ : List<&2, Selection.SlTok>}
      {==}

# the kept glyphs after glyph j are ks, and the model's count past it is n
def src.rb.k(n: Nat, +ks: List<&2, Selection.SlGl>, t: Bool, +g: Nat, +j: Nat, +i: Nat, +eks: {Selection.sl_toks(ks, i) == src.sp(1n+j, n, i) : List<&2, Selection.SlTok>}, +ok: {LS.ls.nbok(n, 1n+j) == True{} : Bool}) -> {Selection.sl_toks(Selection.sl_keep.k(ks, t, Selection.SlGl{j, g}), i) == src.sp(j, M.nb.pick(n, M.counts(t, g), j), i) : List<&2, Selection.SlTok>}:
  match n:
    case 0n:
      %Equal.sym(List<&2, Selection.SlGl>, ks, Nil{}, src.toks_nil(ks, i, Equal.trans(List<&2, Selection.SlTok>, Selection.sl_toks(ks, i), src.sp(1n+j, 0n, i), Nil{}, eks, src.sp_zero(1n+j, 0n, i, LS.ls.le_zero(1n+j))))) : {Selection.sl_toks(Selection.sl_keep.k(_, t, Selection.SlGl{j, g}), i) == src.sp(j, M.nb.pick(0n, M.counts(t, g), j), i) : List<&2, Selection.SlTok>}
      src.last1(t, g, j, i)
    case 1n++p:
      +jp = LS.ls.le_trans(j, 1n+j, p, LS.ls.le_succ(j), ok)
      +span = Selection.sl_span(Nat.sub(p, j), i, 1n+j)
      src.rb.cons(ks, t, g, j, i, p, Equal.trans(List<&2, Selection.SlTok>, Selection.sl_toks(ks, i), src.sp(1n+j, 1n+p, i), span, eks, src.rb.sp(j, p, i, jp)), jp, ok)

def src.rb.at(b: Bool, +g: Nat, +rest: List<&2, Nat>, +c: Nat, +j: Nat, +to: Maybe<&2, Nat>, +t: Bool, +i: Nat, +eb: {M.before(c, to) == b : Bool}, ih: {Selection.sl_toks(Selection.sl_keep(src.colf(rest, M.gnext(g, c), 1n+j, None{}, to), t), i) == src.sp(1n+j, M.row_nb(rest, M.gnext(g, c), 1n+j, to, t), i) : List<&2, Selection.SlTok>}) -> {Selection.sl_toks(Selection.sl_keep(Selection.sl_pick.k(Bool.and(b, True{}), Selection.SlGl{j, g}, src.colf(rest, M.gnext(g, c), 1n+j, None{}, to)), t), i) == src.sp(j, M.nb.pick(M.row_nb(rest, M.gnext(g, c), 1n+j, to, t), Bool.and(b, M.counts(t, g)), j), i) : List<&2, Selection.SlTok>}:
  match b:
    case False{}:
      %Equal.sym(List<&2, Selection.SlGl>, src.colf(rest, M.gnext(g, c), 1n+j, None{}, to), Nil{}, src.colf_out(rest, M.gnext(g, c), 1n+j, None{}, to, src.before_mono(c, M.gnext(g, c), to, eb, src.c_le_next(g, c)))) : {Selection.sl_toks(Selection.sl_keep(_, t), i) == src.sp(j, M.nb.pick(M.row_nb(rest, M.gnext(g, c), 1n+j, to, t), False{}, j), i) : List<&2, Selection.SlTok>}
      %Equal.sym(Nat, M.row_nb(rest, M.gnext(g, c), 1n+j, to, t), 0n, src.nb_out(rest, M.gnext(g, c), 1n+j, to, t, src.before_mono(c, M.gnext(g, c), to, eb, src.c_le_next(g, c)))) : {Nil{} == src.sp(j, M.nb.pick(_, False{}, j), i) : List<&2, Selection.SlTok>}
      Equal.sym(List<&2, Selection.SlTok>, src.sp(j, 0n, i), Nil{}, src.sp_zero(j, 0n, i, LS.ls.le_zero(j)))
    case True{}:
      src.rb.k(M.row_nb(rest, M.gnext(g, c), 1n+j, to, t), Selection.sl_keep(src.colf(rest, M.gnext(g, c), 1n+j, None{}, to), t), t, g, j, i, ih, src.nbok(rest, M.gnext(g, c), 1n+j, to, t))

# past `from`: the tokens of the kept glyphs are the model's span from j
def src.rb(gs: List<&2, Nat>, +c: Nat, +j: Nat, +to: Maybe<&2, Nat>, +t: Bool, +i: Nat) -> {Selection.sl_toks(Selection.sl_keep(src.colf(gs, c, j, None{}, to), t), i) == src.sp(j, M.row_nb(gs, c, j, to, t), i) : List<&2, Selection.SlTok>}:
  match gs:
    case Nil{}:
      Equal.sym(List<&2, Selection.SlTok>, src.sp(j, 0n, i), Nil{}, src.sp_zero(j, 0n, i, LS.ls.le_zero(j)))
    case Con{+g, +rest}:
      src.rb.at(M.before(c, to), g, rest, c, j, to, t, i, {==}, src.rb(rest, M.gnext(g, c), 1n+j, to, t, i))

def src.and_false(b: Bool) -> {False{} == Bool.and(b, False{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a glyph before `from`: dropped by both; the model's count past it adds
# at most this index, and the range starts past it
def src.ra.miss(n: Nat, h: Bool, +L: Nat, +j: Nat, +i: Nat, ge: {Nat.is_le(1n+j, L) == True{} : Bool}) -> {src.sp(L, M.nb.pick(n, h, j), i) == src.sp(L, n, i) : List<&2, Selection.SlTok>}:
  match n:
    case 0n:
      match h:
        case True{}:
          Equal.trans(List<&2, Selection.SlTok>, src.sp(L, 1n+j, i), Nil{}, src.sp(L, 0n, i), src.sp_zero(L, 1n+j, i, ge), Equal.sym(List<&2, Selection.SlTok>, src.sp(L, 0n, i), Nil{}, src.sp_zero(L, 0n, i, LS.ls.le_zero(L))))
        case False{}:
          {==}
    case 1n+p:
      {==}

def src.ra.at(r: Bool, +g: Nat, +rest: List<&2, Nat>, +c: Nat, +j: Nat, +from: Maybe<&2, Nat>, +to: Maybe<&2, Nat>, +t: Bool, +i: Nat, er: {M.reach(from, g, c) == r : Bool}, ih: {Selection.sl_toks(Selection.sl_keep(src.colf(rest, M.gnext(g, c), 1n+j, from, to), t), i) == src.sp(M.row_lo(rest, M.gnext(g, c), 1n+j, from), M.row_nb(rest, M.gnext(g, c), 1n+j, to, t), i) : List<&2, Selection.SlTok>}) -> {Selection.sl_toks(Selection.sl_keep(Selection.sl_pick.k(Bool.and(M.before(c, to), r), Selection.SlGl{j, g}, src.colf(rest, M.gnext(g, c), 1n+j, from, to)), t), i) == src.sp(M.lo.pick(r, j, M.row_lo(rest, M.gnext(g, c), 1n+j, from)), M.row_nb(g <> rest, c, j, to, t), i) : List<&2, Selection.SlTok>}:
  match r:
    case True{}:
      %Equal.sym(List<&2, Selection.SlGl>, src.colf(rest, M.gnext(g, c), 1n+j, from, to), src.colf(rest, M.gnext(g, c), 1n+j, None{}, to), src.colf_from(rest, M.gnext(g, c), 1n+j, from, to, src.reach_next(from, g, c, er))) : {Selection.sl_toks(Selection.sl_keep(Selection.sl_pick.k(Bool.and(M.before(c, to), True{}), Selection.SlGl{j, g}, _), t), i) == src.sp(j, M.row_nb(g <> rest, c, j, to, t), i) : List<&2, Selection.SlTok>}
      src.rb(g <> rest, c, j, to, t, i)
    case False{}:
      +L = M.row_lo(rest, M.gnext(g, c), 1n+j, from)
      %src.and_false(M.before(c, to)) : {Selection.sl_toks(Selection.sl_keep(Selection.sl_pick.k(_, Selection.SlGl{j, g}, src.colf(rest, M.gnext(g, c), 1n+j, from, to)), t), i) == src.sp(L, M.row_nb(g <> rest, c, j, to, t), i) : List<&2, Selection.SlTok>}
      %Equal.sym(List<&2, Selection.SlTok>, Selection.sl_toks(Selection.sl_keep(src.colf(rest, M.gnext(g, c), 1n+j, from, to), t), i), src.sp(L, M.row_nb(rest, M.gnext(g, c), 1n+j, to, t), i), ih) : {_ == src.sp(L, M.row_nb(g <> rest, c, j, to, t), i) : List<&2, Selection.SlTok>}
      Equal.sym(List<&2, Selection.SlTok>, src.sp(L, M.nb.pick(M.row_nb(rest, M.gnext(g, c), 1n+j, to, t), Bool.and(M.before(c, to), M.counts(t, g)), j), i), src.sp(L, M.row_nb(rest, M.gnext(g, c), 1n+j, to, t), i), src.ra.miss(M.row_nb(rest, M.gnext(g, c), 1n+j, to, t), Bool.and(M.before(c, to), M.counts(t, g)), L, j, i, src.lo_ge(rest, M.gnext(g, c), 1n+j, from)))

# the tokens of a row's picked glyphs, the trailing blanks dropped when t,
# are the span of the model's range
def src.range(gs: List<&2, Nat>, +c: Nat, +j: Nat, +from: Maybe<&2, Nat>, +to: Maybe<&2, Nat>, +t: Bool, +i: Nat) -> {Selection.sl_toks(Selection.sl_keep(src.colf(gs, c, j, from, to), t), i) == src.sp(M.row_lo(gs, c, j, from), M.row_nb(gs, c, j, to, t), i) : List<&2, Selection.SlTok>}:
  match gs:
    case Nil{}:
      Equal.sym(List<&2, Selection.SlTok>, src.sp(j, 0n, i), Nil{}, src.sp_zero(j, 0n, i, LS.ls.le_zero(j)))
    case Con{+g, +rest}:
      src.ra.at(M.reach(from, g, c), g, rest, c, j, from, to, t, i, {==}, src.range(rest, M.gnext(g, c), 1n+j, from, to, t, i))
