# eukhe: the proof of LAW settle_run_exact
#
# PROOF: a hit is hit_spec (induction on the lines; on the line hit,
# pend_after_exact), then induction on the outcomes.

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ./pend_after_exact.bend as PPendAfterExact

def srx.hit(ps: List<&2, C.Pend>, k: Nat, +o: C.Outcome) -> {C.hit(ps, k, o) == Compactor.hit_spec(ps, k, o) : List<&2, C.Pend>}:
  match ps:
    case Nil{}:
      {==}
    case +p <> rest:
      match k:
        case 0n:
          %Compactor.pend_after_exact(p, o) : {C.Pend.after(p, o) <> rest == _ <> rest : List<&2, C.Pend>}
          {==}
        case 1n+j:
          %srx.hit(rest, j, o) : {p <> C.hit(rest, j, o) == p <> _ : List<&2, C.Pend>}
          {==}

def srx.go(es: List<&2, C.End>, +ps: List<&2, C.Pend>) -> {C.run(es, ps) == Compactor.settle_spec(es, ps) : List<&2, C.Pend>}:
  match es:
    case Nil{}:
      {==}
    case e <> rest:
      match e:
        case C.End{+k, +o}:
          %srx.hit(ps, k, o) : {C.run(rest, C.hit(ps, k, o)) == Compactor.settle_spec(rest, _) : List<&2, C.Pend>}
          srx.go(rest, C.hit(ps, k, o))

def Compactor.settle_run_exact(es, ps):
  srx.go(es, ps)
