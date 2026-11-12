# eukhe: the proof of LAW sel_drag_scrolls_down
#
# While a selection is being made the scroll step is M.pan of the drag's
# cell (LD.sdg.held); a row below hi with lo <= hi is not above lo
# (LD.sdg.le_lt, LD.sdg.lt_asym), so it asks for a step down.

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ../../laws/selection/drag.bend as SelectionDrag
import ./base.bend as LS
import ./base/drag.bend as LD

def sdd.down(+r: Nat, +c: Nat, +lo: Nat, +hi: Nat, ok: {Nat.is_le(lo, hi) == True{} : Bool}, +below: {Nat.is_lt(hi, r) == True{} : Bool}) -> {M.pan(M.Cell{r, c}, lo, hi) == M.PanDown{} : M.Pan}:
  +na = LD.sdg.lt_asym(lo, r, LD.sdg.le_lt(lo, hi, r, ok, below))
  %Equal.sym(Bool, Nat.is_lt(r, lo), False{}, na) : {Bool.pick(M.Pan, _, M.PanUp{}, Bool.pick(M.Pan, Nat.is_lt(hi, r), M.PanDown{}, M.PanNone{})) == M.PanDown{} : M.Pan}
  %Equal.sym(Bool, Nat.is_lt(hi, r), True{}, below) : {Bool.pick(M.Pan, False{}, M.PanUp{}, Bool.pick(M.Pan, _, M.PanDown{}, M.PanNone{})) == M.PanDown{} : M.Pan}
  {==}

def SelectionDrag.sel_drag_scrolls_down(m, last, r, c, lo, hi, held, ok, below):
  Equal.trans(M.Pan, Selection.sl_pan_of(M.step(M.St{m, last}, M.EvDrag{M.Cell{r, c}, lo, hi})), M.pan(M.Cell{r, c}, lo, hi), M.PanDown{}, LD.sdg.held(m, last, M.Cell{r, c}, lo, hi, held), sdd.down(r, c, lo, hi, ok, below))
