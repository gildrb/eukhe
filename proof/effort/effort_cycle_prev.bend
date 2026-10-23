# eukhe: the proof of LAW effort_cycle_prev

import Base
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pe.effort_cycle_prev(+m: Ef.Mdl, +pre: List<&2, Ef.Lv>, +a: Ef.Lv, +b: Ef.Lv, +post: List<&2, Ef.Lv>, +split: {Ef.offered(m) == List.append(&2, Ef.Lv, pre, a <> b <> post) : List<&2, Ef.Lv>}) -> {Ef.cycle(m, b, Ef.Backward{}) == Some{a} : Maybe<&2, Ef.Lv>}:
  %Equal.sym(List<&2, Ef.Lv>, Ef.offered(m), List.append(&2, Ef.Lv, pre, a <> b <> post), split) : {Ef.cycle.in(_, b, Ef.Backward{}) == Some{a} : Maybe<&2, Ef.Lv>}
  LA.pe.prev(pre, a, b, post, LA.pe.asc_tr(Ef.offered(m), List.append(&2, Ef.Lv, pre, a <> b <> post), split, LA.pe.effort_offered_asc(m)))

def Laws.effort_cycle_prev(m, pre, a, b, post, split):
  pe.effort_cycle_prev(m, pre, a, b, post, split)
