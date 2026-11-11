# eukhe: the proof of LAW glob_utf8_layout
#
# PROOF: per length branch of the code (below 0x80, 0x800, 0x10000), both
# sides compute equal.

import Base
import ../../laws/glob.bend as Glob
import ./base/utf8.bend as GU

def Glob.glob_utf8_layout(x, rest):
  GU.u8.b(x, rest, U32.is_lt(x, 128))
