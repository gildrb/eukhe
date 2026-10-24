# eukhe: the proof of LAW selection_ffi_open

import Base
import ../../bend/ffi_selection.bend as F
import ../../laws/selection.bend as Selection

# W.end of "" is True and of a char then more is False; the refused
# state answers its error at once
def Selection.selection_ffi_open(c, rest, input):
  ({==}, ({==}, {==}))
