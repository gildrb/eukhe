# eukhe: the proof of LAW sel_drag_moves_head

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection
import ./base.bend as LS

# per mode, with the cells as constructors: both sides compute the same
# clamp, scroll step and comparisons; a picked range's anchor stays a
# choice, and the answers built on it agree by LS.ls.moved
def Selection.sel_drag_moves_head(m, last, at, lo, hi):
  match m:
    case M.Idle{}:
      {==}
    case M.Pressed{a}:
      match a:
        case M.Cell{ar, ac}:
          match at:
            case M.Cell{r, c}:
              {==}
    case M.Selecting{a, h}:
      match a:
        case M.Cell{ar, ac}:
          match at:
            case M.Cell{r, c}:
              {==}
    case M.Picked{g}:
      match g:
        case M.Rng{s, e}:
          match s:
            case M.Cell{+sr, +sc}:
              match at:
                case M.Cell{+r, +c}:
                  LS.ls.moved(M.Selecting{Bool.pick(M.Cell, M.cell_le(M.Cell{sr, sc}, M.clamp(M.Cell{r, c}, lo, hi)), M.Cell{sr, sc}, e), M.clamp(M.Cell{r, c}, lo, hi)}, M.pan(M.Cell{r, c}, lo, hi))
    case M.Shown{g}:
      {==}
