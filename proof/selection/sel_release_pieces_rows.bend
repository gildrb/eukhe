# eukhe: the proof of LAW sel_release_pieces_rows
#
# The premises make the mode a drag or a pick whose range is r1:c1..r2:c2.
# M.copy walks the release rows counting down the rows left (copy.go) and
# makes one piece per row; the spec takes the first 1 + r2 - r1 rows. The
# first piece's first glyph is M.row_lo, a search for the first glyph that
# reaches the start column: that is the count of glyphs that end before it
# (fp.lo), since every glyph after one that reaches it reaches it too
# (fp.none). Later rows start at glyph 0; every piece ends at or past its
# start (fp.fwd).

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ../../laws/selection/reply.bend as SelectionReply
import ./base.bend as LS

# the end of a piece is at or past its first glyph
def fp.fwd(x: Bool, +lo: Nat, nb: Nat, e: {Nat.is_le(lo, nb) == x : Bool}) -> {Nat.is_le(lo, M.max.pick(x, lo, nb)) == True{} : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      LS.ls.le_refl(lo)

# a not at most b: b is below a
def fp.nle_lt(a: Nat, b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n q:
      LS.ls.absurd({Nat.is_lt(q, 0n) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_le(0n, q), True{}, Equal.sym(Bool, Nat.is_le(0n, q), False{}, h), LS.ls.le_zero(q)))
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      fp.nle_lt(p, q, h)

# glyphs from column c on, with x at most c: none ends before x
def fp.none(gs: List<&2, Nat>, +c: Nat, +x: Nat, +h: {Nat.is_le(x, c) == True{} : Bool}) -> {SelectionReply.sl_before(gs, c, x) == 0n : Nat}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, +rest}:
      match g:
        case 0n:
          %Equal.sym(Bool, Nat.is_lt(c, x), False{}, LS.ls.le_nlt(x, c, h)) : {SelectionReply.sl_before.k(_, SelectionReply.sl_before(rest, 1n+c, x)) == 0n : Nat}
          fp.none(rest, 1n+c, x, LS.ls.le_trans(x, c, 1n+c, h, LS.ls.le_succ(c)))
        case 1n++p:
          +L = Nat.add(p, c)
          +hl = LS.ls.le_trans(x, c, L, h, LS.ls.le_add(p, c))
          %Equal.sym(Bool, Nat.is_lt(L, x), False{}, LS.ls.le_nlt(x, L, hl)) : {SelectionReply.sl_before.k(_, SelectionReply.sl_before(rest, 1n+L, x)) == 0n : Nat}
          fp.none(rest, 1n+L, x, LS.ls.le_trans(x, L, 1n+L, hl, LS.ls.le_succ(L)))

# one glyph ending at column L: it reaches x (the search stops at j, and no
# later glyph ends before x) or it ends before x (one more to count)
def fp.at(+L: Nat, +j: Nat, +x: Nat, +rest: List<&2, Nat>, b: Bool, +eb: {Nat.is_le(x, L) == b : Bool}, ih: {M.row_lo(rest, 1n+L, 1n+j, Some{x}) == Nat.add(SelectionReply.sl_before(rest, 1n+L, x), 1n+j) : Nat}) -> {M.lo.pick(b, j, M.row_lo(rest, 1n+L, 1n+j, Some{x})) == Nat.add(SelectionReply.sl_before.k(Nat.is_lt(L, x), SelectionReply.sl_before(rest, 1n+L, x)), j) : Nat}:
  match b:
    case True{}:
      %Equal.sym(Bool, Nat.is_lt(L, x), False{}, LS.ls.le_nlt(x, L, eb)) : {j == Nat.add(SelectionReply.sl_before.k(_, SelectionReply.sl_before(rest, 1n+L, x)), j) : Nat}
      %Equal.sym(Nat, SelectionReply.sl_before(rest, 1n+L, x), 0n, fp.none(rest, 1n+L, x, LS.ls.le_trans(x, L, 1n+L, eb, LS.ls.le_succ(L)))) : {j == Nat.add(_, j) : Nat}
      {==}
    case False{}:
      +B = SelectionReply.sl_before(rest, 1n+L, x)
      %Equal.sym(Bool, Nat.is_lt(L, x), True{}, fp.nle_lt(x, L, eb)) : {M.row_lo(rest, 1n+L, 1n+j, Some{x}) == Nat.add(SelectionReply.sl_before.k(_, B), j) : Nat}
      Equal.trans(Nat, M.row_lo(rest, 1n+L, 1n+j, Some{x}), Nat.add(B, 1n+j), 1n+Nat.add(B, j), ih, LS.ls.add_succ(B, j))

# the first glyph that reaches column x is j plus the count of glyphs that
# end before x
def fp.lo(gs: List<&2, Nat>, +c: Nat, +j: Nat, +x: Nat) -> {M.row_lo(gs, c, j, Some{x}) == Nat.add(SelectionReply.sl_before(gs, c, x), j) : Nat}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, +rest}:
      match g:
        case 0n:
          fp.at(c, j, x, rest, Nat.is_le(x, c), {==}, fp.lo(rest, 1n+c, 1n+j, x))
        case 1n++p:
          fp.at(Nat.add(p, c), j, x, rest, Nat.is_le(x, Nat.add(p, c)), {==}, fp.lo(rest, 1n+Nat.add(p, c), 1n+j, x))

# with no start column the first glyph is glyph 0
def fp.lo0(gs: List<&2, Nat>, +c: Nat) -> {M.row_lo(gs, c, 0n, None{}) == 0n : Nat}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, rest}:
      {==}

def fp.brk(w: M.Wrap) -> {M.not_cont(w) == Selection.sl_brk(w) : Bool}:
  match w:
    case M.Single{}:
      {==}
    case M.Head{}:
      {==}
    case M.Cont{}:
      {==}

def fp.cons(-a: SelectionReply.SlFrame, -b: SelectionReply.SlFrame, -xs: List<&2, SelectionReply.SlFrame>, -ys: List<&2, SelectionReply.SlFrame>, h1: {a == b : SelectionReply.SlFrame}, h2: {xs == ys : List<&2, SelectionReply.SlFrame>}) -> {a <> xs == b <> ys : List<&2, SelectionReply.SlFrame>}:
  %h1 : {a <> xs == _ <> ys : List<&2, SelectionReply.SlFrame>}
  %h2 : {a <> xs == a <> _ : List<&2, SelectionReply.SlFrame>}
  {==}

def fp.one(-a: SelectionReply.SlFrame, -b: SelectionReply.SlFrame, h: {a == b : SelectionReply.SlFrame}) -> {[a] == [b] : List<&2, SelectionReply.SlFrame>}:
  %h : {[a] == [_] : List<&2, SelectionReply.SlFrame>}
  {==}

# a piece, framed: its row, first glyph, newline, and forward
def fp.piece(+w: M.Wrap, +gs: List<&2, Nat>, +i: Nat, +from: Maybe<&2, Nat>, +to: Maybe<&2, Nat>, +trim: Bool, +first: Bool) -> {SelectionReply.sl_frame(M.piece(M.Row{w, gs}, i, from, to, trim, first)) == SelectionReply.SlFrame{i, M.row_lo(gs, 0n, 0n, from), Bool.and(Bool.not(first), M.not_cont(w)), True{}} : SelectionReply.SlFrame}:
  +lo = M.row_lo(gs, 0n, 0n, from)
  +nb = M.row_nb(gs, 0n, 0n, to, trim)
  +nl = Bool.and(Bool.not(first), M.not_cont(w))
  %fp.fwd(Nat.is_le(lo, nb), lo, nb, {==}) : {SelectionReply.SlFrame{i, lo, nl, Nat.is_le(lo, M.max.pick(Nat.is_le(lo, nb), lo, nb))} == SelectionReply.SlFrame{i, lo, nl, _} : SelectionReply.SlFrame}
  {==}

# the first row of the copy
def fp.head(+w: M.Wrap, +gs: List<&2, Nat>, +x: Nat, +to: Maybe<&2, Nat>, +trim: Bool) -> {SelectionReply.sl_frame(M.piece(M.Row{w, gs}, 0n, Some{x}, to, trim, True{})) == SelectionReply.SlFrame{0n, SelectionReply.sl_before(gs, 0n, x), False{}, True{}} : SelectionReply.SlFrame}:
  +B = SelectionReply.sl_before(gs, 0n, x)
  +el = Equal.trans(Nat, M.row_lo(gs, 0n, 0n, Some{x}), Nat.add(B, 0n), B, fp.lo(gs, 0n, 0n, x), LS.ls.add_zero(B))
  Equal.trans(SelectionReply.SlFrame, SelectionReply.sl_frame(M.piece(M.Row{w, gs}, 0n, Some{x}, to, trim, True{})), SelectionReply.SlFrame{0n, M.row_lo(gs, 0n, 0n, Some{x}), False{}, True{}}, SelectionReply.SlFrame{0n, B, False{}, True{}}, fp.piece(w, gs, 0n, Some{x}, to, trim, True{}), Equal.cong(Nat, SelectionReply.SlFrame, z => SelectionReply.SlFrame{0n, z, False{}, True{}}, M.row_lo(gs, 0n, 0n, Some{x}), B, el))

# a later row of the copy
def fp.later(+w: M.Wrap, +gs: List<&2, Nat>, +i: Nat, +to: Maybe<&2, Nat>, +trim: Bool) -> {SelectionReply.sl_frame(M.piece(M.Row{w, gs}, 1n+i, None{}, to, trim, False{})) == SelectionReply.SlFrame{1n+i, 0n, Selection.sl_brk(w), True{}} : SelectionReply.SlFrame}:
  %fp.brk(w) : {SelectionReply.sl_frame(M.piece(M.Row{w, gs}, 1n+i, None{}, to, trim, False{})) == SelectionReply.SlFrame{1n+i, 0n, _, True{}} : SelectionReply.SlFrame}
  %fp.lo0(gs, 0n) : {SelectionReply.sl_frame(M.piece(M.Row{w, gs}, 1n+i, None{}, to, trim, False{})) == SelectionReply.SlFrame{1n+i, _, M.not_cont(w), True{}} : SelectionReply.SlFrame}
  fp.piece(w, gs, 1n+i, None{}, to, trim, False{})

# a later row, the last of the copy
def fp.t0(row: M.Row, rest: List<&2, M.Row>, +i: Nat, +c2: Nat) -> {SelectionReply.sl_frame_list(M.copy.go(Con{row, rest}, 1n+i, 0n, None{}, c2, False{})) == SelectionReply.sl_frames_later(List.take(&2, M.Row, Con{row, rest}, 1n), 1n+i) : List<&2, SelectionReply.SlFrame>}:
  match row:
    case M.Row{+w, +gs}:
      match rest:
        case Nil{}:
          fp.one(SelectionReply.sl_frame(M.piece(M.Row{w, gs}, 1n+i, None{}, Some{c2}, True{}, False{})), SelectionReply.SlFrame{1n+i, 0n, Selection.sl_brk(w), True{}}, fp.later(w, gs, i, Some{c2}, True{}))
        case Con{y, ys}:
          fp.one(SelectionReply.sl_frame(M.piece(M.Row{w, gs}, 1n+i, None{}, Some{c2}, True{}, False{})), SelectionReply.SlFrame{1n+i, 0n, Selection.sl_brk(w), True{}}, fp.later(w, gs, i, Some{c2}, True{}))

# a later row with more after it
def fp.tm(row: M.Row, +rest: List<&2, M.Row>, +i: Nat, +m: Nat, +c2: Nat, ih: {SelectionReply.sl_frame_list(M.copy.go(rest, 2n+i, m, None{}, c2, False{})) == SelectionReply.sl_frames_later(List.take(&2, M.Row, rest, 1n+m), 2n+i) : List<&2, SelectionReply.SlFrame>}) -> {SelectionReply.sl_frame_list(M.copy.go(Con{row, rest}, 1n+i, 1n+m, None{}, c2, False{})) == SelectionReply.sl_frames_later(List.take(&2, M.Row, Con{row, rest}, 2n+m), 1n+i) : List<&2, SelectionReply.SlFrame>}:
  match row:
    case M.Row{+w, +gs}:
      fp.cons(SelectionReply.sl_frame(M.piece(M.Row{w, gs}, 1n+i, None{}, None{}, M.rest_blank(rest, m, c2), False{})), SelectionReply.SlFrame{1n+i, 0n, Selection.sl_brk(w), True{}}, SelectionReply.sl_frame_list(M.copy.go(rest, 2n+i, m, None{}, c2, False{})), SelectionReply.sl_frames_later(List.take(&2, M.Row, rest, 1n+m), 2n+i), fp.later(w, gs, i, None{}, M.rest_blank(rest, m, c2)), ih)

# the rows after the first: one frame per row of the first 1 + k
def fp.tail(rows: List<&2, M.Row>, +i: Nat, k: Nat, +c2: Nat) -> {SelectionReply.sl_frame_list(M.copy.go(rows, 1n+i, k, None{}, c2, False{})) == SelectionReply.sl_frames_later(List.take(&2, M.Row, rows, 1n+k), 1n+i) : List<&2, SelectionReply.SlFrame>}:
  match rows k:
    case Nil{} k:
      {==}
    case Con{row, rest} 0n:
      fp.t0(row, rest, i, c2)
    case Con{row, +rest} 1n++m:
      fp.tm(row, rest, i, m, c2, fp.tail(rest, 1n+i, m, c2))

# the first row, the last of the copy
def fp.g0(row: M.Row, rest: List<&2, M.Row>, +x: Nat, +c2: Nat) -> {SelectionReply.sl_frame_list(M.copy.go(Con{row, rest}, 0n, 0n, Some{x}, c2, True{})) == SelectionReply.sl_frames_first(List.take(&2, M.Row, Con{row, rest}, 1n), x) : List<&2, SelectionReply.SlFrame>}:
  match row:
    case M.Row{+w, +gs}:
      match rest:
        case Nil{}:
          fp.one(SelectionReply.sl_frame(M.piece(M.Row{w, gs}, 0n, Some{x}, Some{c2}, True{}, True{})), SelectionReply.SlFrame{0n, SelectionReply.sl_before(gs, 0n, x), False{}, True{}}, fp.head(w, gs, x, Some{c2}, True{}))
        case Con{y, ys}:
          fp.one(SelectionReply.sl_frame(M.piece(M.Row{w, gs}, 0n, Some{x}, Some{c2}, True{}, True{})), SelectionReply.SlFrame{0n, SelectionReply.sl_before(gs, 0n, x), False{}, True{}}, fp.head(w, gs, x, Some{c2}, True{}))

# the first row with more after it
def fp.gm(row: M.Row, +rest: List<&2, M.Row>, +x: Nat, +m: Nat, +c2: Nat, ih: {SelectionReply.sl_frame_list(M.copy.go(rest, 1n, m, None{}, c2, False{})) == SelectionReply.sl_frames_later(List.take(&2, M.Row, rest, 1n+m), 1n) : List<&2, SelectionReply.SlFrame>}) -> {SelectionReply.sl_frame_list(M.copy.go(Con{row, rest}, 0n, 1n+m, Some{x}, c2, True{})) == SelectionReply.sl_frames_first(List.take(&2, M.Row, Con{row, rest}, 2n+m), x) : List<&2, SelectionReply.SlFrame>}:
  match row:
    case M.Row{+w, +gs}:
      fp.cons(SelectionReply.sl_frame(M.piece(M.Row{w, gs}, 0n, Some{x}, None{}, M.rest_blank(rest, m, c2), True{})), SelectionReply.SlFrame{0n, SelectionReply.sl_before(gs, 0n, x), False{}, True{}}, SelectionReply.sl_frame_list(M.copy.go(rest, 1n, m, None{}, c2, False{})), SelectionReply.sl_frames_later(List.take(&2, M.Row, rest, 1n+m), 1n), fp.head(w, gs, x, None{}, M.rest_blank(rest, m, c2)), ih)

# the rows of the copy, from its first: one frame per row of the first 1 + k
def fp.go(rows: List<&2, M.Row>, k: Nat, +x: Nat, +c2: Nat) -> {SelectionReply.sl_frame_list(M.copy.go(rows, 0n, k, Some{x}, c2, True{})) == SelectionReply.sl_frames_first(List.take(&2, M.Row, rows, 1n+k), x) : List<&2, SelectionReply.SlFrame>}:
  match rows k:
    case Nil{} k:
      {==}
    case Con{row, rest} 0n:
      fp.g0(row, rest, x, c2)
    case Con{row, +rest} 1n++m:
      fp.gm(row, rest, x, m, c2, fp.tail(rest, 0n, m, c2))

def fp.rows(below: Bool, rows: List<&2, M.Row>, k: Nat, +c1: Nat, +c2: Nat) -> {SelectionReply.sl_frame_list(M.copy.rows(below, rows, k, c1, c2)) == Bool.pick(List<&2, SelectionReply.SlFrame>, below, Nil{}, SelectionReply.sl_frames_first(List.take(&2, M.Row, rows, 1n+k), c1)) : List<&2, SelectionReply.SlFrame>}:
  match below:
    case True{}:
      {==}
    case False{}:
      fp.go(rows, k, c1, c2)

# the copy of the range r1:c1..r2:c2, framed
def fp.copy(+r1: Nat, +c1: Nat, +r2: Nat, +c2: Nat, rows: List<&2, M.Row>) -> {SelectionReply.sl_frame_list(M.copy(M.Rng{M.Cell{r1, c1}, M.Cell{r2, c2}}, rows)) == SelectionReply.sl_frames_of(r1, c1, r2, rows) : List<&2, SelectionReply.SlFrame>}:
  fp.rows(Nat.is_lt(r2, r1), rows, Nat.sub(r2, r1), c1, c2)

def fp.get(m: Maybe<&2, M.Rng>, d: M.Rng) -> M.Rng:
  match m:
    case None{}:
      d
    case Some{v}:
      v

def fp.unsome(+x: M.Rng, +y: M.Rng, e: {Some{x} == Some{y} : Maybe<&2, M.Rng>}) -> {x == y : M.Rng}:
  Equal.cong(Maybe<&2, M.Rng>, M.Rng, z => fp.get(z, x), Some{x}, Some{y}, e)

def fp.MIf(m: Maybe<&2, M.Rng>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{v}:
      G

def fp.none_some(-G: Type, -y: M.Rng, e: {None{} == Some{y} : Maybe<&2, M.Rng>}) -> G:
  %e : fp.MIf(_, G)
  Unit{}

# the frames of the copy of a range equal to r1:c1..r2:c2
def fp.of(+r: M.Rng, +r1: Nat, +c1: Nat, +r2: Nat, +c2: Nat, rows: List<&2, M.Row>, e: {r == M.Rng{M.Cell{r1, c1}, M.Cell{r2, c2}} : M.Rng}) -> {Some{SelectionReply.sl_frame_list(M.copy(r, rows))} == Some{SelectionReply.sl_frames_of(r1, c1, r2, rows)} : Maybe<&2, List<&2, SelectionReply.SlFrame>>}:
  %Equal.sym(M.Rng, r, M.Rng{M.Cell{r1, c1}, M.Cell{r2, c2}}, e) : {Some{SelectionReply.sl_frame_list(M.copy(_, rows))} == Some{SelectionReply.sl_frames_of(r1, c1, r2, rows)} : Maybe<&2, List<&2, SelectionReply.SlFrame>>}
  Equal.cong(List<&2, SelectionReply.SlFrame>, Maybe<&2, List<&2, SelectionReply.SlFrame>>, xs => Some{xs}, SelectionReply.sl_frame_list(M.copy(M.Rng{M.Cell{r1, c1}, M.Cell{r2, c2}}, rows)), SelectionReply.sl_frames_of(r1, c1, r2, rows), fp.copy(r1, c1, r2, c2, rows))

def SelectionReply.sel_release_pieces_rows(m, last, rows, r1, c1, r2, c2, held, shown):
  match m:
    case M.Idle{}:
      LS.ls.absurd({SelectionReply.sl_frames(M.step(M.St{M.Idle{}, last}, M.EvRelease{rows})) == Some{SelectionReply.sl_frames_of(r1, c1, r2, rows)} : Maybe<&2, List<&2, SelectionReply.SlFrame>>}, held)
    case M.Pressed{a}:
      fp.none_some({SelectionReply.sl_frames(M.step(M.St{M.Pressed{a}, last}, M.EvRelease{rows})) == Some{SelectionReply.sl_frames_of(r1, c1, r2, rows)} : Maybe<&2, List<&2, SelectionReply.SlFrame>>}, M.Rng{M.Cell{r1, c1}, M.Cell{r2, c2}}, shown)
    case M.Selecting{+a, +h}:
      +R = {M.Rng{M.Cell{r1, c1}, M.Cell{r2, c2}} : M.Rng}
      fp.of(M.order(a, h), r1, c1, r2, c2, rows, Equal.trans(M.Rng, M.order(a, h), Selection.sl_order(a, h), R, LS.ls.order(a, h), fp.unsome(Selection.sl_order(a, h), R, shown)))
    case M.Picked{+r}:
      fp.of(r, r1, c1, r2, c2, rows, fp.unsome(r, M.Rng{M.Cell{r1, c1}, M.Cell{r2, c2}}, shown))
    case M.Shown{r}:
      LS.ls.absurd({SelectionReply.sl_frames(M.step(M.St{M.Shown{r}, last}, M.EvRelease{rows})) == Some{SelectionReply.sl_frames_of(r1, c1, r2, rows)} : Maybe<&2, List<&2, SelectionReply.SlFrame>>}, held)
