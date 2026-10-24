# eukhe: the proof of LAW failures_exact

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor

def fle.go(os: List<&2, C.Outcome>) -> {C.failures(os) == Compactor.failures_spec(os) : Nat}:
  match os:
    case Nil{}:
      {==}
    case o <> +rest:
      match o:
        case C.Built{}:
          fle.go(rest)
        case C.Failed{}:
          %Equal.sym(Nat, C.failures(rest), Compactor.failures_spec(rest), fle.go(rest)) : {1n+_ == 1n+Compactor.failures_spec(rest) : Nat}
          {==}
        case C.Disk{}:
          fle.go(rest)
        case C.Stopped{}:
          fle.go(rest)

def Compactor.failures_exact(os):
  fle.go(os)
