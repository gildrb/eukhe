# eukhe: the proof of LAW effort_cycle_still

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort.bend as Effort

def pe.effort_cycle_still(+m: Ef.Mdl, +l: Ef.Lv, +d: Ef.Dir, few: {Ef.two(Ef.offered(m)) == False{} : Bool}) -> {Ef.cycle(m, l, d) == None{} : Maybe<&2, Ef.Lv>}:
  %Equal.sym(Bool, Ef.two(Ef.offered(m)), False{}, few) : {Ef.cycle.at(_, Ef.offered(m), l, d) == None{} : Maybe<&2, Ef.Lv>}
  {==}

def Effort.effort_cycle_still(m, l, d, few):
  pe.effort_cycle_still(m, l, d, few)
