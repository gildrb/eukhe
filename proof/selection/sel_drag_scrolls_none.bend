# eukhe: the proof of LAW sel_drag_scrolls_none
#
# With no selection being made (idle, shown) a drag answers no scroll step;
# while one is, the premise says the row is neither above lo nor below hi,
# and M.pan of the drag's cell (LD.sdg.held) is then none.

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ../../laws/selection/drag.bend as SelectionDrag
import ./base.bend as LS
import ./base/drag.bend as LD

def sdn.none(+r: Nat, +c: Nat, +lo: Nat, +hi: Nat, +still: {Bool.or(Nat.is_lt(r, lo), Nat.is_lt(hi, r)) == False{} : Bool}) -> {M.pan(M.Cell{r, c}, lo, hi) == M.PanNone{} : M.Pan}:
  %Equal.sym(Bool, Nat.is_lt(r, lo), False{}, LD.sdg.or_l(Nat.is_lt(r, lo), Nat.is_lt(hi, r), still)) : {Bool.pick(M.Pan, _, M.PanUp{}, Bool.pick(M.Pan, Nat.is_lt(hi, r), M.PanDown{}, M.PanNone{})) == M.PanNone{} : M.Pan}
  %Equal.sym(Bool, Nat.is_lt(hi, r), False{}, LD.sdg.or_r(Nat.is_lt(r, lo), Nat.is_lt(hi, r), still)) : {Bool.pick(M.Pan, False{}, M.PanUp{}, Bool.pick(M.Pan, _, M.PanDown{}, M.PanNone{})) == M.PanNone{} : M.Pan}
  {==}

def sdn.held(m: M.Mode, +last: Maybe<&2, M.Click>, +r: Nat, +c: Nat, +lo: Nat, +hi: Nat, held: {Selection.sl_held(m) == True{} : Bool}, still: {Bool.or(Nat.is_lt(r, lo), Nat.is_lt(hi, r)) == False{} : Bool}) -> {Selection.sl_pan_of(M.step(M.St{m, last}, M.EvDrag{M.Cell{r, c}, lo, hi})) == M.PanNone{} : M.Pan}:
  Equal.trans(M.Pan, Selection.sl_pan_of(M.step(M.St{m, last}, M.EvDrag{M.Cell{r, c}, lo, hi})), M.pan(M.Cell{r, c}, lo, hi), M.PanNone{}, LD.sdg.held(m, last, M.Cell{r, c}, lo, hi, held), sdn.none(r, c, lo, hi, still))

def SelectionDrag.sel_drag_scrolls_none(m, last, r, c, lo, hi, still):
  match m:
    case M.Idle{}:
      {==}
    case M.Pressed{a}:
      sdn.held(M.Pressed{a}, last, r, c, lo, hi, {==}, still)
    case M.Selecting{a, h}:
      sdn.held(M.Selecting{a, h}, last, r, c, lo, hi, {==}, still)
    case M.Picked{g}:
      sdn.held(M.Picked{g}, last, r, c, lo, hi, {==}, still)
    case M.Shown{g}:
      {==}
