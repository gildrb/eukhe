# eukhe: the proof of LAW glob_bytes
#
# PROOF: both sides compute equal once the char is opened.

import Base
import ../../laws/glob.bend as Glob

def Glob.glob_bytes(c, t):
  match c:
    case Chr{x}:
      {==}
