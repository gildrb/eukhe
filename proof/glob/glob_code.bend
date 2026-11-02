# eukhe: the proof of LAW glob_code
#
# PROOF: both sides compute equal once the char is opened.

import Base
import ../../laws/glob.bend as Glob

def Glob.glob_code(c):
  match c:
    case Chr{x}:
      {==}
