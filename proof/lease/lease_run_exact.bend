# eukhe: the proof of LAW lease_run_exact
# By induction on the events: each step is the laws' (lease_step_exact).

import Base
import ../../bend/lease.bend as Ls
import ../../laws/lease.bend as Lease
import ./lease_step_exact.bend as PStep

def sr.go(evs: List<&2, Ls.Ev>, +s: Ls.L) -> {Ls.go(evs, s) == Lease.lw_go(evs, s) : Ls.L}:
  match evs:
    case Nil{}:
      {==}
    case +e <> t:
      %Lease.lease_step_exact(s, e) : {Ls.go(t, Ls.step(s, e)) == Lease.lw_go(t, _) : Ls.L}
      sr.go(t, Ls.step(s, e))

def Lease.lease_run_exact(evs, s):
  (sr.go(evs, s), {==})
