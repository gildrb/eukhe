# eukhe: the proof of LAW restart_failures_exact

import Base
import ../../bend/supervise.bend as Su
import ../../laws/supervise.bend as Supervise
import ./base.bend as LA

def Supervise.restart_failures_exact(c, gs):
  %LA.ps.rs_go(c, gs, Su.St{Nil{}, 0n}) : {Su.St.n(Su.go(c, gs, Su.St{Nil{}, 0n})) == Supervise.restart_count(_) : Nat}
  LA.ps.rs_count(Su.go(c, gs, Su.St{Nil{}, 0n}))
