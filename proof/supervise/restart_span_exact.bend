# eukhe: the proof of LAW restart_span_exact

import Base
import ../../bend/supervise.bend as Su
import ../../laws/supervise.bend as Supervise
import ./base.bend as LA
import ../base/nat.bend as LNat

def Supervise.restart_span_exact(gs):
  %LNat.add_zero(Supervise.restart_sum(gs)) : {Su.span.go(gs, 0n) == _ : Nat}
  LA.ps.rs_span(gs, 0n)
