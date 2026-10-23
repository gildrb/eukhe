# eukhe: the proof of LAW effort_cycle_wrap_back

import Base
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pe.effort_cycle_wrap_back(+m: Ef.Mdl, +h: Ef.Lv, +pre: List<&2, Ef.Lv>, +z: Ef.Lv, split: {Ef.offered(m) == List.append(&2, Ef.Lv, h <> pre, [z]) : List<&2, Ef.Lv>}) -> {Ef.cycle(m, h, Ef.Backward{}) == Some{z} : Maybe<&2, Ef.Lv>}:
  %Equal.sym(List<&2, Ef.Lv>, Ef.offered(m), List.append(&2, Ef.Lv, h <> pre, [z]), split) : {Ef.cycle.in(_, h, Ef.Backward{}) == Some{z} : Maybe<&2, Ef.Lv>}
  LA.pe.wrap_back(h, pre, z)

def Laws.effort_cycle_wrap_back(m, h, pre, z, split):
  pe.effort_cycle_wrap_back(m, h, pre, z, split)
