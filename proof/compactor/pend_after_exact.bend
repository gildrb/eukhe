# eukhe: the proof of LAW pend_after_exact

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor

def pae.failed(k: Nat) -> {C.Owed.after(C.Failed{}, k) == Compactor.after_spec.failed(k) : C.Pend}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      {==}

def Compactor.pend_after_exact(p, o):
  match p:
    case C.Made{}:
      {==}
    case C.Owed{k}:
      match o:
        case C.Built{}:
          {==}
        case C.Failed{}:
          pae.failed(k)
        case C.Disk{}:
          {==}
        case C.Stopped{}:
          {==}
