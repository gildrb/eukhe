# eukhe: the proof of LAW sel_release_pieces
#
# M.copy walks the release rows (copy.go) and makes one piece per row: its
# first glyph is M.row_lo, the first glyph that reaches the start column
# (row 0) or 0 (later rows: no start column), its end at or past it
# (max.pick), its newline when it is not the first and does not continue
# the row above. Row by row that is the spec's frame.

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ../../laws/selection/reply.bend as SelectionReply

def fp.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      fp.le_refl(p)

# the end of a piece is at or past its first glyph
def fp.fwd(x: Bool, +lo: Nat, nb: Nat, e: {Nat.is_le(lo, nb) == x : Bool}) -> {Nat.is_le(lo, M.max.pick(x, lo, nb)) == True{} : Bool}:
  match x:
    case True{}:
      e
    case False{}:
      fp.le_refl(lo)

def fp.pick(b: Bool, -j: Nat, x: Nat, -y: Nat, e: {x == y : Nat}) -> {M.lo.pick(b, j, x) == SelectionReply.sl_first.k(b, j, y) : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      e

# the first glyph that reaches column x
def fp.lo(gs: List<&2, Nat>, +c: Nat, +j: Nat, +x: Nat) -> {M.row_lo(gs, c, j, Some{x}) == SelectionReply.sl_first(gs, c, j, x) : Nat}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, +rest}:
      match g:
        case 0n:
          fp.pick(Nat.is_le(x, c), j, M.row_lo(rest, 1n+c, 1n+j, Some{x}), SelectionReply.sl_first(rest, 1n+c, 1n+j, x), fp.lo(rest, 1n+c, 1n+j, x))
        case 1n++p:
          fp.pick(Nat.is_le(x, Nat.add(p, c)), j, M.row_lo(rest, 1n+Nat.add(p, c), 1n+j, Some{x}), SelectionReply.sl_first(rest, 1n+Nat.add(p, c), 1n+j, x), fp.lo(rest, 1n+Nat.add(p, c), 1n+j, x))

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
def fp.head(row: M.Row, +x: Nat, +to: Maybe<&2, Nat>, +trim: Bool) -> {SelectionReply.sl_frame(M.piece(row, 0n, Some{x}, to, trim, True{})) == SelectionReply.sl_row_frame(row, 0n, x) : SelectionReply.SlFrame}:
  match row:
    case M.Row{+w, +gs}:
      %fp.lo(gs, 0n, 0n, x) : {SelectionReply.sl_frame(M.piece(M.Row{w, gs}, 0n, Some{x}, to, trim, True{})) == SelectionReply.SlFrame{0n, _, False{}, True{}} : SelectionReply.SlFrame}
      fp.piece(w, gs, 0n, Some{x}, to, trim, True{})

# a later row of the copy
def fp.later(row: M.Row, +i: Nat, -x: Nat, +to: Maybe<&2, Nat>, +trim: Bool) -> {SelectionReply.sl_frame(M.piece(row, 1n+i, None{}, to, trim, False{})) == SelectionReply.sl_row_frame(row, 1n+i, x) : SelectionReply.SlFrame}:
  match row:
    case M.Row{+w, +gs}:
      %fp.brk(w) : {SelectionReply.sl_frame(M.piece(M.Row{w, gs}, 1n+i, None{}, to, trim, False{})) == SelectionReply.SlFrame{1n+i, 0n, _, True{}} : SelectionReply.SlFrame}
      %fp.lo0(gs, 0n) : {SelectionReply.sl_frame(M.piece(M.Row{w, gs}, 1n+i, None{}, to, trim, False{})) == SelectionReply.SlFrame{1n+i, _, M.not_cont(w), True{}} : SelectionReply.SlFrame}
      fp.piece(w, gs, 1n+i, None{}, to, trim, False{})

# the rows after the first
def fp.tail(rows: List<&2, M.Row>, +i: Nat, k: Nat, +x: Nat, +c2: Nat) -> {SelectionReply.sl_frame_list(M.copy.go(rows, 1n+i, k, None{}, c2, False{})) == SelectionReply.sl_frame_rows(rows, 1n+i, k, x) : List<&2, SelectionReply.SlFrame>}:
  match rows k:
    case Nil{} k:
      {==}
    case Con{+row, rest} 0n:
      fp.one(SelectionReply.sl_frame(M.piece(row, 1n+i, None{}, Some{c2}, True{}, False{})), SelectionReply.sl_row_frame(row, 1n+i, x), fp.later(row, i, x, Some{c2}, True{}))
    case Con{+row, +rest} 1n++m:
      fp.cons(SelectionReply.sl_frame(M.piece(row, 1n+i, None{}, None{}, M.rest_blank(rest, m, c2), False{})), SelectionReply.sl_row_frame(row, 1n+i, x), SelectionReply.sl_frame_list(M.copy.go(rest, 2n+i, m, None{}, c2, False{})), SelectionReply.sl_frame_rows(rest, 2n+i, m, x), fp.later(row, i, x, None{}, M.rest_blank(rest, m, c2)), fp.tail(rest, 1n+i, m, x, c2))

# the rows of the copy, from its first
def fp.go(rows: List<&2, M.Row>, k: Nat, +x: Nat, +c2: Nat) -> {SelectionReply.sl_frame_list(M.copy.go(rows, 0n, k, Some{x}, c2, True{})) == SelectionReply.sl_frame_rows(rows, 0n, k, x) : List<&2, SelectionReply.SlFrame>}:
  match rows k:
    case Nil{} k:
      {==}
    case Con{+row, rest} 0n:
      fp.one(SelectionReply.sl_frame(M.piece(row, 0n, Some{x}, Some{c2}, True{}, True{})), SelectionReply.sl_row_frame(row, 0n, x), fp.head(row, x, Some{c2}, True{}))
    case Con{+row, +rest} 1n++m:
      fp.cons(SelectionReply.sl_frame(M.piece(row, 0n, Some{x}, None{}, M.rest_blank(rest, m, c2), True{})), SelectionReply.sl_row_frame(row, 0n, x), SelectionReply.sl_frame_list(M.copy.go(rest, 1n, m, None{}, c2, False{})), SelectionReply.sl_frame_rows(rest, 1n, m, x), fp.head(row, x, None{}, M.rest_blank(rest, m, c2)), fp.tail(rest, 0n, m, x, c2))

def fp.rows(below: Bool, rows: List<&2, M.Row>, k: Nat, +c1: Nat, +c2: Nat) -> {SelectionReply.sl_frame_list(M.copy.rows(below, rows, k, c1, c2)) == SelectionReply.sl_frame_rng.k(below, rows, k, c1) : List<&2, SelectionReply.SlFrame>}:
  match below:
    case True{}:
      {==}
    case False{}:
      fp.go(rows, k, c1, c2)

# the copy of every range, framed
def fp.copy(r: M.Rng, rows: List<&2, M.Row>) -> {SelectionReply.sl_frame_list(M.copy(r, rows)) == SelectionReply.sl_frame_rng(r, rows) : List<&2, SelectionReply.SlFrame>}:
  match r:
    case M.Rng{a, b}:
      match a:
        case M.Cell{+r1, c1}:
          match b:
            case M.Cell{+r2, c2}:
              fp.rows(Nat.is_lt(r2, r1), rows, Nat.sub(r2, r1), c1, c2)

def SelectionReply.sel_release_pieces(m, last, rows):
  match m:
    case M.Idle{}:
      {==}
    case M.Pressed{a}:
      {==}
    case M.Selecting{a, h}:
      match a:
        case M.Cell{+ar, +ac}:
          match h:
            case M.Cell{+hr, +hc}:
              +r = M.order(M.Cell{ar, ac}, M.Cell{hr, hc})
              Equal.cong(List<&2, SelectionReply.SlFrame>, Maybe<&2, List<&2, SelectionReply.SlFrame>>, xs => Some{xs}, SelectionReply.sl_frame_list(M.copy(r, rows)), SelectionReply.sl_frame_rng(r, rows), fp.copy(r, rows))
    case M.Picked{r}:
      Equal.cong(List<&2, SelectionReply.SlFrame>, Maybe<&2, List<&2, SelectionReply.SlFrame>>, xs => Some{xs}, SelectionReply.sl_frame_list(M.copy(r, rows)), SelectionReply.sl_frame_rng(r, rows), fp.copy(r, rows))
    case M.Shown{r}:
      {==}
