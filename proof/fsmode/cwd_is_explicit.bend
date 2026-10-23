# eukhe: the proof of LAW cwd_is_explicit

import Base
import ../../LAWS.bend as Laws
import ../base.bend as L

def Laws.cwd_is_explicit(c, p, ok):
  L.explicit(c, p, ok)
