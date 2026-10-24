# eukhe: the proof of LAW sel_click_copies_nothing

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection

# with no last press the press counts 1 and holds the button (Pressed);
# its release goes back to Idle and keeps the press
def Selection.sel_click_copies_nothing(m, at, t, gs, rows):
  {==}
