# eukhe: the proof of LAW sel_esc_clears

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection

# per mode: the model spends Esc exactly when the mode shows a selection
def Selection.sel_esc_clears(m, last):
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
