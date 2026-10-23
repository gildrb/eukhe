# eukhe: the proof of LAW cwd_is_explicit

import Base
import ../../laws/fsmode.bend as Fsmode
import ../base.bend as L

def Fsmode.cwd_is_explicit(c, p, ok):
  L.explicit(c, p, ok)
