# eukhe: the proof of LAW guard_cuts_loops

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ./base.bend as LA

def pi.guard_cuts_loops(+xs: List<&2, Nat>, +k: Nat, lp: {If.loops(xs, k) == True{} : Bool}) -> {If.Cut.cut(If.guard(xs, k)) == True{} : Bool}:
  LA.pi.cut_go(xs, k, Nil{}, 0n, If.fire.at(xs, k, Nil{}), {==}, lp)

def Infer.guard_cuts_loops(xs, k, lp):
  pi.guard_cuts_loops(xs, k, lp)
