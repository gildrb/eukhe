# eukhe: the proof of LAW sel_copy_anchor_to_head

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ./base.bend as LS
import ./sel_release_copies.bend as PSelReleaseCopies

# A first press holds the button at a (Pressed); a drag to a cell h on
# screen keeps h (the clamp moves nothing) and, h being another cell,
# selects from a to h; the release copies that range (LAW
# sel_release_copies).

def scah.clamp(+hr: Nat, +hc: Nat, +lo: Nat, +hi: Nat, l1: {Nat.is_lt(hr, lo) == False{} : Bool}, l2: {Nat.is_lt(hi, hr) == False{} : Bool}) -> {M.clamp(M.Cell{hr, hc}, lo, hi) == M.Cell{hr, hc} : M.Cell}:
  %Equal.sym(Bool, Nat.is_lt(hr, lo), False{}, l1) : {M.Cell{Bool.pick(Nat, _, lo, Bool.pick(Nat, Nat.is_lt(hi, hr), hi, hr)), hc} == M.Cell{hr, hc} : M.Cell}
  %Equal.sym(Bool, Nat.is_lt(hi, hr), False{}, l2) : {M.Cell{Bool.pick(Nat, _, hi, hr), hc} == M.Cell{hr, hc} : M.Cell}
  {==}

def scah.drag(+A: M.Cell, +hr: Nat, +hc: Nat, +lo: Nat, +hi: Nat, last: Maybe<&2, M.Click>, l1: {Nat.is_lt(hr, lo) == False{} : Bool}, l2: {Nat.is_lt(hi, hr) == False{} : Bool}, ne: {M.cell_eq(A, M.Cell{hr, hc}) == False{} : Bool}) -> {Selection.sl_st(M.step(M.St{M.Pressed{A}, last}, M.EvDrag{M.Cell{hr, hc}, lo, hi})) == M.St{M.Selecting{A, M.Cell{hr, hc}}, None{}} : M.St}:
  +H = {M.Cell{hr, hc} : M.Cell}
  +PAN = M.pan(H, lo, hi)
  %Equal.sym(M.Cell, M.clamp(H, lo, hi), H, scah.clamp(hr, hc, lo, hi, l1, l2)) : {Selection.sl_st(Bool.pick(M.Res, M.cell_eq(A, _), M.moved(M.Pressed{A}, PAN), M.moved(M.Selecting{A, _}, PAN))) == M.St{M.Selecting{A, H}, None{}} : M.St}
  %Equal.sym(Bool, M.cell_eq(A, H), False{}, ne) : {Selection.sl_st(Bool.pick(M.Res, _, M.moved(M.Pressed{A}, PAN), M.moved(M.Selecting{A, H}, PAN))) == M.St{M.Selecting{A, H}, None{}} : M.St}
  {==}

def Selection.sel_copy_anchor_to_head(m, a, t, gs, h, lo, hi, rows, on, moved):
  match a:
    case M.Cell{+ar, +ac}:
      match h:
        case M.Cell{+hr, +hc}:
          +A = {M.Cell{ar, ac} : M.Cell}
          +H = {M.Cell{hr, hc} : M.Cell}
          +hon = on
          +l1 = LS.ls.le_nlt(lo, hr, LS.ls.and_l(Nat.is_le(lo, hr), Nat.is_le(hr, hi), hon))
          +l2 = LS.ls.le_nlt(hr, hi, LS.ls.and_r(Nat.is_le(lo, hr), Nat.is_le(hr, hi), hon))
          %Equal.sym(M.St, Selection.sl_st(M.step(M.St{M.Pressed{A}, Some{M.Click{A, t, 1n}}}, M.EvDrag{H, lo, hi})), M.St{M.Selecting{A, H}, None{}}, scah.drag(A, hr, hc, lo, hi, Some{M.Click{A, t, 1n}}, l1, l2, moved)) : {Selection.sl_copied(M.step(_, M.EvRelease{rows})) == Some{Selection.sl_copy(Selection.sl_order(A, H), rows)} : Maybe<&2, List<&2, Selection.SlTok>>}
          Pair.fst({Selection.sl_copied(M.step(M.St{M.Selecting{A, H}, None{}}, M.EvRelease{rows})) == Selection.sl_release_copy(M.Selecting{A, H}, rows) : Maybe<&2, List<&2, Selection.SlTok>>}, {Selection.sl_uncopied(M.step(M.St{M.Selecting{A, H}, None{}}, M.EvRelease{rows})) == Selection.sl_release(M.Selecting{A, H}, None{}) : M.Res}, Selection.sel_release_copies(M.Selecting{A, H}, None{}, rows))
