# eukhe: the proof of LAW once_entry_open_exact
#
# PROOF: the end check computes on the empty input and on an input with
# a first char.

import Base
import ../../laws/once.bend as Once

def Once.once_entry_open_exact(c, i):
  ({==}, {==})
