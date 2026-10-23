# eukhe: the proof of LAW effort_cycle_next

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort.bend as Effort
import ./base.bend as LA

def pe.effort_cycle_next(+m: Ef.Mdl, +pre: List<&2, Ef.Lv>, +a: Ef.Lv, +b: Ef.Lv, +post: List<&2, Ef.Lv>, +split: {Ef.offered(m) == List.append(&2, Ef.Lv, pre, a <> b <> post) : List<&2, Ef.Lv>}) -> {Ef.cycle(m, a, Ef.Forward{}) == Some{b} : Maybe<&2, Ef.Lv>}:
  %Equal.sym(List<&2, Ef.Lv>, Ef.offered(m), List.append(&2, Ef.Lv, pre, a <> b <> post), split) : {Ef.cycle.in(_, a, Ef.Forward{}) == Some{b} : Maybe<&2, Ef.Lv>}
  LA.pe.next(pre, a, b, post, LA.pe.asc_tr(Ef.offered(m), List.append(&2, Ef.Lv, pre, a <> b <> post), split, LA.pe.effort_offered_asc(m)))

def Effort.effort_cycle_next(m, pre, a, b, post, split):
  pe.effort_cycle_next(m, pre, a, b, post, split)
