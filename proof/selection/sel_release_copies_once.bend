# eukhe: the proof of LAW sel_release_copies_once

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection

# per mode: a release leaves nothing being made (Idle or Shown), and a
# release there copies nothing
def Selection.sel_release_copies_once(s, rows, more):
  match s:
    case M.St{m, last}:
      match m:
        case M.Idle{}:
          {==}
        case M.Pressed{a}:
          {==}
        case M.Selecting{a, h}:
          {==}
        case M.Picked{r}:
          {==}
        case M.Shown{r}:
          {==}
