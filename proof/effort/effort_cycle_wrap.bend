# eukhe: the proof of LAW effort_cycle_wrap

import Base
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pe.effort_cycle_wrap(+m: Ef.Mdl, +h: Ef.Lv, +pre: List<&2, Ef.Lv>, +z: Ef.Lv, +split: {Ef.offered(m) == List.append(&2, Ef.Lv, h <> pre, [z]) : List<&2, Ef.Lv>}) -> {Ef.cycle(m, z, Ef.Forward{}) == Some{h} : Maybe<&2, Ef.Lv>}:
  %Equal.sym(List<&2, Ef.Lv>, Ef.offered(m), List.append(&2, Ef.Lv, h <> pre, [z]), split) : {Ef.cycle.in(_, z, Ef.Forward{}) == Some{h} : Maybe<&2, Ef.Lv>}
  LA.pe.wrap(h, pre, z, LA.pe.asc_tr(Ef.offered(m), List.append(&2, Ef.Lv, h <> pre, [z]), split, LA.pe.effort_offered_asc(m)))

def Laws.effort_cycle_wrap(m, h, pre, z, split):
  pe.effort_cycle_wrap(m, h, pre, z, split)
