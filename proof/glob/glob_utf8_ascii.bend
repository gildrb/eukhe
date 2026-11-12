# eukhe: the proof of LAW glob_utf8_ascii
#
# PROOF: a code below 0x80 takes the one-byte branch.

import Base
import ../../bend/glob/items.bend as GItems
import ../../laws/glob.bend as Glob

def Glob.glob_utf8_ascii(x, rest, h):
  %Equal.sym(Bool, U32.is_lt(x, 128), True{}, h) : {GItems.utf8.b(x, rest, _) == x <> rest : List<&2, U32>}
  {==}
