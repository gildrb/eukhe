# eukhe: the proof of LAW sel_key_clears

import Base
import ../../bend/selection.bend as M
import ../../laws/selection.bend as Selection

# every state answers a key, a wheel notch and a content change with the
# cleared answer, at once
def Selection.sel_key_clears(s):
  match s:
    case M.St{m, last}:
      ({==}, ({==}, {==}))
