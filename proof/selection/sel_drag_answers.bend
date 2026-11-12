# eukhe: the proof of LAW sel_drag_answers
#
# Every answer the code gives a drag is M.quiet or M.moved of its mode with
# the last press forgotten; M.moved is the spec's sl_moved (LS.ls.moved),
# and a press's two answers are each that form (sda.pick).

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ../../laws/selection/drag.bend as SelectionDrag
import ./base.bend as LS

# an answer kept as its mode and scroll step say
def sda.Form(r: M.Res) -> Type:
  {r == Selection.sl_moved(Selection.sl_mode(r), Selection.sl_pan_of(r)) : M.Res}

def sda.pick(b: Bool, +x: M.Res, +y: M.Res, hx: sda.Form(x), hy: sda.Form(y)) -> sda.Form(Bool.pick(M.Res, b, x, y)):
  match b:
    case True{}:
      hx
    case False{}:
      hy

def SelectionDrag.sel_drag_answers(m, last, at, lo, hi):
  match m:
    case M.Idle{}:
      {==}
    case M.Pressed{+a}:
      +h = M.clamp(at, lo, hi)
      +p = M.pan(at, lo, hi)
      sda.pick(M.cell_eq(a, h), M.moved(M.Pressed{a}, p), M.moved(M.Selecting{a, h}, p), LS.ls.moved(M.Pressed{a}, p), LS.ls.moved(M.Selecting{a, h}, p))
    case M.Selecting{+a, x}:
      LS.ls.moved(M.Selecting{a, M.clamp(at, lo, hi)}, M.pan(at, lo, hi))
    case M.Picked{g}:
      match g:
        case M.Rng{+s, +e}:
          +h = M.clamp(at, lo, hi)
          LS.ls.moved(M.Selecting{Bool.pick(M.Cell, M.cell_le(s, h), s, e), h}, M.pan(at, lo, hi))
    case M.Shown{g}:
      {==}
