# eukhe: the proof of LAW read_exact

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor

def rde.go(n: Nat, rs: List<&2, C.Reply>) -> {C.read(n, rs) == Compactor.read_spec(n, rs) : List<&2, C.Reply>}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      match rs:
        case Nil{}:
          {==}
        case +r <> +rest:
          %Equal.sym(List<&2, C.Reply>, C.read(p, rest), Compactor.read_spec(p, rest), rde.go(p, rest)) : {r <> _ == r <> Compactor.read_spec(p, rest) : List<&2, C.Reply>}
          {==}

def Compactor.read_exact(n, rs):
  rde.go(n, rs)
