# eukhe: the proof of LAW sel_drag_scrolls_up
#
# While a selection is being made the scroll step is M.pan of the drag's
# cell (LD.sdg.held), and a row above lo asks for a step up.

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ../../laws/selection/drag.bend as SelectionDrag
import ./base.bend as LS
import ./base/drag.bend as LD

def sdu.up(+r: Nat, +c: Nat, +lo: Nat, +hi: Nat, above: {Nat.is_lt(r, lo) == True{} : Bool}) -> {M.pan(M.Cell{r, c}, lo, hi) == M.PanUp{} : M.Pan}:
  %Equal.sym(Bool, Nat.is_lt(r, lo), True{}, above) : {Bool.pick(M.Pan, _, M.PanUp{}, Bool.pick(M.Pan, Nat.is_lt(hi, r), M.PanDown{}, M.PanNone{})) == M.PanUp{} : M.Pan}
  {==}

def SelectionDrag.sel_drag_scrolls_up(m, last, r, c, lo, hi, held, above):
  Equal.trans(M.Pan, Selection.sl_pan_of(M.step(M.St{m, last}, M.EvDrag{M.Cell{r, c}, lo, hi})), M.pan(M.Cell{r, c}, lo, hi), M.PanUp{}, LD.sdg.held(m, last, M.Cell{r, c}, lo, hi, held), sdu.up(r, c, lo, hi, above))
