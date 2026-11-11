# eukhe: the proof of LAW sel_line_copies_row
#
# The third press picks the row 0..E (sel_line_picks_row), and its release
# copies sl_copy of that range over the row (sel_release_copies). On the row
# itself every glyph has a cell in 0..E, since the row's glyphs end at
# column 1 + E and each glyph's column is at most where the glyphs after it
# end (slc.mono); so the copy picks every glyph (slc.pick).

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ./base.bend as LS
import ./sel_line_picks_row.bend as PL
import ./sel_release_copies.bend as PRC

# the glyphs from column c end at or past c
def slc.mono(gs: List<&2, Nat>, +c: Nat) -> {Nat.is_le(c, M.width(gs, c)) == True{} : Bool}:
  match gs:
    case Nil{}:
      LS.ls.le_refl(c)
    case Con{g, +rest}:
      match g:
        case 0n:
          LS.ls.le_trans(c, 1n+c, M.width(rest, 1n+c), LS.ls.le_succ(c), slc.mono(rest, 1n+c))
        case 1n++p:
          +L = Nat.add(p, c)
          LS.ls.le_trans(c, 1n+L, M.width(rest, 1n+L), LS.ls.le_trans(c, L, 1n+L, LS.ls.le_add(p, c), LS.ls.le_succ(L)), slc.mono(rest, 1n+L))

# a cell of row r at column c is at or before r:E when c <= E
def slc.le_row(+r: Nat, +c: Nat, +E: Nat, h: {Nat.is_le(c, E) == True{} : Bool}) -> {Selection.sl_le(M.Cell{r, c}, M.Cell{r, E}) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_lt(r, r), False{}, LS.ls.lt_irrefl(r)) : {Bool.or(_, Bool.and(Nat.is_eq(r, r), Nat.is_le(c, E))) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_eq(r, r), True{}, LS.ls.eq_refl(r)) : {Bool.or(False{}, Bool.and(_, Nat.is_le(c, E))) == True{} : Bool}
  h

# one glyph at column c with last cell L, the glyphs after it from column
# 1 + L: picked, then the rest
def slc.one(+g: Nat, +c: Nat, +L: Nat, +j: Nat, +r: Nat, +E: Nat, +rest: List<&2, Nat>, hc: {Nat.is_le(c, E) == True{} : Bool}, ih: {Selection.sl_pick(rest, 1n+L, 1n+j, r, M.Cell{r, 0n}, M.Cell{r, E}) == Selection.sl_glyphs(rest, 1n+j) : List<&2, Selection.SlGl>}) -> {Selection.sl_pick.k(Bool.and(Selection.sl_le(M.Cell{r, c}, M.Cell{r, E}), Selection.sl_le(M.Cell{r, 0n}, M.Cell{r, L})), Selection.SlGl{j, g}, Selection.sl_pick(rest, 1n+L, 1n+j, r, M.Cell{r, 0n}, M.Cell{r, E})) == Selection.SlGl{j, g} <> Selection.sl_glyphs(rest, 1n+j) : List<&2, Selection.SlGl>}:
  %Equal.sym(Bool, Selection.sl_le(M.Cell{r, c}, M.Cell{r, E}), True{}, slc.le_row(r, c, E, hc)) : {Selection.sl_pick.k(Bool.and(_, Selection.sl_le(M.Cell{r, 0n}, M.Cell{r, L})), Selection.SlGl{j, g}, Selection.sl_pick(rest, 1n+L, 1n+j, r, M.Cell{r, 0n}, M.Cell{r, E})) == Selection.SlGl{j, g} <> Selection.sl_glyphs(rest, 1n+j) : List<&2, Selection.SlGl>}
  %Equal.sym(Bool, Selection.sl_le(M.Cell{r, 0n}, M.Cell{r, L}), True{}, slc.le_row(r, 0n, L, LS.ls.le_zero(L))) : {Selection.sl_pick.k(Bool.and(True{}, _), Selection.SlGl{j, g}, Selection.sl_pick(rest, 1n+L, 1n+j, r, M.Cell{r, 0n}, M.Cell{r, E})) == Selection.SlGl{j, g} <> Selection.sl_glyphs(rest, 1n+j) : List<&2, Selection.SlGl>}
  Equal.cong(List<&2, Selection.SlGl>, List<&2, Selection.SlGl>, z => Selection.SlGl{j, g} <> z, Selection.sl_pick(rest, 1n+L, 1n+j, r, M.Cell{r, 0n}, M.Cell{r, E}), Selection.sl_glyphs(rest, 1n+j), ih)

# the glyphs gs from column c, ending at column 1 + E, all have a cell in
# 0..E of row r: each is picked
def slc.pick(gs: List<&2, Nat>, +c: Nat, +j: Nat, +r: Nat, +E: Nat, +e: {M.width(gs, c) == 1n+E : Nat}) -> {Selection.sl_pick(gs, c, j, r, M.Cell{r, 0n}, M.Cell{r, E}) == Selection.sl_glyphs(gs, j) : List<&2, Selection.SlGl>}:
  match gs:
    case Nil{}:
      {==}
    case Con{g, +rest}:
      match g:
        case 0n:
          +W = M.width(rest, 1n+c)
          +hm = Equal.trans(Bool, Nat.is_le(1n+c, 1n+E), Nat.is_le(1n+c, W), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(1n+c, z), 1n+E, W, Equal.sym(Nat, W, 1n+E, e)), slc.mono(rest, 1n+c))
          slc.one(0n, c, c, j, r, E, rest, hm, slc.pick(rest, 1n+c, 1n+j, r, E, e))
        case 1n++p:
          +L = Nat.add(p, c)
          +W = M.width(rest, 1n+L)
          +hm = Equal.trans(Bool, Nat.is_le(1n+L, 1n+E), Nat.is_le(1n+L, W), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(1n+L, z), 1n+E, W, Equal.sym(Nat, W, 1n+E, e)), slc.mono(rest, 1n+L))
          slc.one(1n+p, c, L, j, r, E, rest, LS.ls.le_trans(c, L, E, LS.ls.le_add(p, c), hm), slc.pick(rest, 1n+L, 1n+j, r, E, e))

# the copy of the row's range 0..E over the row alone: every glyph, its
# trailing blanks dropped
def slc.copy(+w: M.Wrap, +gs: List<&2, Nat>, +r: Nat, +E: Nat, e: {M.width(gs, 0n) == 1n+E : Nat}) -> {Selection.sl_copy(M.Rng{M.Cell{r, 0n}, M.Cell{r, E}}, [M.Row{w, gs}]) == Selection.sl_toks(Selection.sl_keep(Selection.sl_glyphs(gs, 0n), True{}), 0n) : List<&2, Selection.SlTok>}:
  +a = {M.Cell{r, 0n} : M.Cell}
  +b = {M.Cell{r, E} : M.Cell}
  +X = {Selection.sl_toks(Selection.sl_keep(Selection.sl_pick(gs, 0n, 0n, r, a, b), True{}), 0n) : List<&2, Selection.SlTok>}
  +Y = {Selection.sl_toks(Selection.sl_keep(Selection.sl_glyphs(gs, 0n), True{}), 0n) : List<&2, Selection.SlTok>}
  %Equal.sym(Bool, Nat.is_le(r, r), True{}, LS.ls.le_refl(r)) : {Selection.sl_rows.k(_, Selection.sl_row(M.Row{w, gs}, 0n, r, a, b, Bool.or(Nat.is_eq(r, r), True{})), Nil{}) == Y : List<&2, Selection.SlTok>}
  %Equal.sym(Bool, Nat.is_eq(r, r), True{}, LS.ls.eq_refl(r)) : {List.append(&2, Selection.SlTok, Selection.sl_row(M.Row{w, gs}, 0n, r, a, b, Bool.or(_, True{})), Nil{}) == Y : List<&2, Selection.SlTok>}
  %Equal.sym(List<&2, Selection.SlTok>, List.append(&2, Selection.SlTok, X, Nil{}), X, LS.ls.app_nil(X)) : {_ == Y : List<&2, Selection.SlTok>}
  %Equal.sym(List<&2, Selection.SlGl>, Selection.sl_pick(gs, 0n, 0n, r, a, b), Selection.sl_glyphs(gs, 0n), slc.pick(gs, 0n, 0n, r, E, e)) : {Selection.sl_toks(Selection.sl_keep(_, True{}), 0n) == Y : List<&2, Selection.SlTok>}
  {==}

# the first of two facts
def slc.fst(-A: Type, -B: Type, p: A & B) -> A:
  match p:
    case (a, b):
      a

def Selection.sel_line_copies_row(m, r, x, t1, t2, xs, g, w, near):
  +GS = List.append(&2, Nat, xs, [g])
  +E = Selection.sl_last(g, Selection.sl_cells(xs))
  +RG = {M.Rng{M.Cell{r, 0n}, M.Cell{r, E}} : M.Rng}
  +k = {M.Click{M.Cell{r, x}, t2, 3n} : M.Click}
  +rows = {[M.Row{w, GS}] : List<&2, M.Row>}
  +Y = {Selection.sl_toks(Selection.sl_keep(Selection.sl_glyphs(GS, 0n), True{}), 0n) : List<&2, Selection.SlTok>}
  %Equal.sym(M.Res, M.step(M.St{m, Some{M.Click{M.Cell{r, x}, t1, 2n}}}, M.EvPress{M.Cell{r, x}, t2, GS}), Selection.sl_pressed(Some{RG}, M.Cell{r, x}, t2, 3n), Selection.sel_line_picks_row(m, r, x, t1, t2, xs, g, near)) : {Selection.sl_copied(M.step(Selection.sl_st(_), M.EvRelease{rows})) == Some{Y} : Maybe<&2, List<&2, Selection.SlTok>>}
  +c1 = slc.fst({Selection.sl_copied(M.step(M.St{M.Picked{RG}, Some{k}}, M.EvRelease{rows})) == Selection.sl_release_copy(M.Picked{RG}, rows) : Maybe<&2, List<&2, Selection.SlTok>>}, {Selection.sl_uncopied(M.step(M.St{M.Picked{RG}, Some{k}}, M.EvRelease{rows})) == Selection.sl_release(M.Picked{RG}, Some{k}) : M.Res}, Selection.sel_release_copies(M.Picked{RG}, Some{k}, rows))
  Equal.trans(Maybe<&2, List<&2, Selection.SlTok>>, Selection.sl_copied(M.step(M.St{M.Picked{RG}, Some{k}}, M.EvRelease{rows})), Some{Selection.sl_copy(RG, rows)}, Some{Y}, c1, Equal.cong(List<&2, Selection.SlTok>, Maybe<&2, List<&2, Selection.SlTok>>, z => Some{z}, Selection.sl_copy(RG, rows), Y, slc.copy(w, GS, r, E, PL.slp.wlast(xs, g))))
