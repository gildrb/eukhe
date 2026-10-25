# eukhe: the proof of LAW sel_scroll_past_edge

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ./sel_drag_moves_head.bend as PSelDragMovesHead

# The step answers sl_drag (LAW sel_drag_moves_head), whose scroll step is
# sl_drag_pan: per mode; a press's two answers share theirs.

def sse.pick(b: Bool, a: M.Cell, h: M.Cell, p: M.Pan) -> {Selection.sl_pan_of(Bool.pick(M.Res, b, Selection.sl_moved(M.Pressed{a}, p), Selection.sl_moved(M.Selecting{a, h}, p))) == p : M.Pan}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sse.pan(m: M.Mode, +at: M.Cell, +lo: Nat, +hi: Nat) -> {Selection.sl_pan_of(Selection.sl_drag(m, at, lo, hi)) == Selection.sl_drag_pan(m, at, lo, hi) : M.Pan}:
  match m:
    case M.Idle{}:
      {==}
    case M.Pressed{+a}:
      sse.pick(Selection.sl_same(a, Selection.sl_clamp(at, lo, hi)), a, Selection.sl_clamp(at, lo, hi), Selection.sl_pan(at, lo, hi))
    case M.Selecting{a, h}:
      {==}
    case M.Picked{g}:
      match g:
        case M.Rng{s, e}:
          {==}
    case M.Shown{g}:
      {==}

def Selection.sel_scroll_past_edge(m, last, at, lo, hi):
  %Equal.sym(M.Res, M.step(M.St{m, last}, M.EvDrag{at, lo, hi}), Selection.sl_drag(m, at, lo, hi), Selection.sel_drag_moves_head(m, last, at, lo, hi)) : {Selection.sl_pan_of(_) == Selection.sl_drag_pan(m, at, lo, hi) : M.Pan}
  sse.pan(m, at, lo, hi)
