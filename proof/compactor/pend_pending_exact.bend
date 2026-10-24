# eukhe: the proof of LAW pend_pending_exact

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor

def Compactor.pend_pending_exact(p):
  match p:
    case C.Made{}:
      {==}
    case C.Owed{n}:
      {==}
