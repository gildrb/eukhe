# eukhe: the proof of LAW sel_line_picks_row
#
# The third press counts 3 (LS.ls.clicks: next(2)) and picks the row by the
# column after its glyphs, M.width from column 0. That column is the cells
# of the glyphs (slp.width), so for xs then g it is one past the last cell
# of g, which starts after the cells of xs (slp.wlast).

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ./base.bend as LS

# the column after the glyphs gs from column c is c plus their cells
def slp.width(gs: List<&2, Nat>, +c: Nat) -> {M.width(gs, c) == Nat.add(Selection.sl_cells(gs), c) : Nat}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, +rest}:
      match g:
        case 0n:
          Equal.trans(Nat, M.width(rest, 1n+c), Nat.add(Selection.sl_cells(rest), 1n+c), 1n+Nat.add(Selection.sl_cells(rest), c),
            slp.width(rest, 1n+c), LS.ls.add_succ(Selection.sl_cells(rest), c))
        case 1n++p:
          +W = Selection.sl_cells(rest)
          %Equal.sym(Nat, M.width(rest, 1n+Nat.add(p, c)), Nat.add(W, 1n+Nat.add(p, c)), slp.width(rest, 1n+Nat.add(p, c))) : {_ == 1n+Nat.add(Nat.add(p, W), c) : Nat}
          %Equal.sym(Nat, Nat.add(W, 1n+Nat.add(p, c)), 1n+Nat.add(W, Nat.add(p, c)), LS.ls.add_succ(W, Nat.add(p, c))) : {_ == 1n+Nat.add(Nat.add(p, W), c) : Nat}
          %LS.ls.add_assoc(W, p, c) : {1n+_ == 1n+Nat.add(Nat.add(p, W), c) : Nat}
          %LS.ls.add_comm(p, W) : {1n+Nat.add(_, c) == 1n+Nat.add(Nat.add(p, W), c) : Nat}
          {==}

# from column 0: the cells
def slp.w0(+gs: List<&2, Nat>) -> {M.width(gs, 0n) == Selection.sl_cells(gs) : Nat}:
  Equal.trans(Nat, M.width(gs, 0n), Nat.add(Selection.sl_cells(gs), 0n), Selection.sl_cells(gs), slp.width(gs, 0n), LS.ls.add_zero(Selection.sl_cells(gs)))

# the glyphs xs then ys: ys from the column after xs
def slp.width_app(xs: List<&2, Nat>, +ys: List<&2, Nat>, +c: Nat) -> {M.width(List.append(&2, Nat, xs, ys), c) == M.width(ys, M.width(xs, c)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case Con{g, rest}:
      slp.width_app(rest, ys, M.gnext(g, c))

# one glyph g at column C: one past its last cell
def slp.last(g: Nat, +C: Nat) -> {M.width([g], C) == 1n+Selection.sl_last(g, C) : Nat}:
  match g:
    case 0n:
      {==}
    case 1n+p:
      {==}

# the glyphs xs then g from column 0: one past the last cell of g, which
# starts after the cells of xs
def slp.wlast(+xs: List<&2, Nat>, +g: Nat) -> {M.width(List.append(&2, Nat, xs, [g]), 0n) == 1n+Selection.sl_last(g, Selection.sl_cells(xs)) : Nat}:
  +C = Selection.sl_cells(xs)
  +e1 = Equal.cong(Nat, Nat, z => M.width([g], z), M.width(xs, 0n), C, slp.w0(xs))
  Equal.trans(Nat, M.width(List.append(&2, Nat, xs, [g]), 0n), M.width([g], M.width(xs, 0n)), 1n+Selection.sl_last(g, C), slp.width_app(xs, [g], 0n), Equal.trans(Nat, M.width([g], M.width(xs, 0n)), M.width([g], C), 1n+Selection.sl_last(g, C), e1, slp.last(g, C)))

def Selection.sel_line_picks_row(m, r, x, t1, t2, xs, g, near):
  +GS = List.append(&2, Nat, xs, [g])
  +E = Selection.sl_last(g, Selection.sl_cells(xs))
  %Equal.sym(Nat, M.clicks(Some{M.Click{M.Cell{r, x}, t1, 2n}}, M.Cell{r, x}, t2), 3n, LS.ls.clicks(r, x, t1, t2, 2n, near)) : {M.press.go(M.press.mode(_, M.Cell{r, x}, GS), M.Click{M.Cell{r, x}, t2, _}) == Selection.sl_pressed(Some{M.Rng{M.Cell{r, 0n}, M.Cell{r, E}}}, M.Cell{r, x}, t2, 3n) : M.Res}
  %Equal.sym(Nat, M.width(GS, 0n), 1n+E, slp.wlast(xs, g)) : {M.press.go(M.line.of(_, r, x), M.Click{M.Cell{r, x}, t2, 3n}) == Selection.sl_pressed(Some{M.Rng{M.Cell{r, 0n}, M.Cell{r, E}}}, M.Cell{r, x}, t2, 3n) : M.Res}
  {==}
