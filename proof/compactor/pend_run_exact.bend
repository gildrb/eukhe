# eukhe: the proof of LAW pend_run_exact
#
# PROOF: induction on the outcomes; each step is pend_after_exact.

import Base
import ../../bend/compactor.bend as C
import ../../laws/compactor.bend as Compactor
import ./pend_after_exact.bend as PPendAfterExact

def prx.go(os: List<&2, C.Outcome>, +p: C.Pend) -> {C.Pend.run(os, p) == Compactor.pend_run_spec(os, p) : C.Pend}:
  match os:
    case Nil{}:
      {==}
    case +o <> rest:
      %Compactor.pend_after_exact(p, o) : {C.Pend.run(rest, C.Pend.after(p, o)) == Compactor.pend_run_spec(rest, _) : C.Pend}
      prx.go(rest, C.Pend.after(p, o))

def Compactor.pend_run_exact(os, p):
  prx.go(os, p)
