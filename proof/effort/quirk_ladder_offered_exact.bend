# eukhe: the proof of LAW quirk_ladder_offered_exact

import Base
import ../../bend/infer.bend as If
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def pq.quirk_ladder_offered_exact(+explicit: Maybe<&2, Ef.LvMap>, +rule: Maybe<&2, Ef.LvMap>, +d: If.Defaults, +l: Ef.Lv) -> {Ef.has(If.lad.offered(True{}, explicit, rule, d), l) == If.lad.keep(l, Ef.entry(l, If.lad.chosen(explicit, rule)), If.Defaults.reasoning(d)) : Bool}:
  +C = If.lad.chosen(explicit, rule)
  +D = If.Defaults.reasoning(d)
  +F = If.lad.fill(C, D)
  Equal.trans(Bool, Ef.has(Ef.offer(F, Ef.ladder()), l), Ef.keep(F, l), If.lad.keep(l, Ef.entry(l, C), D), LA.pq.lad_has_keep(F, l), L.pq.lad_fill_keep(C, D, l))

def Laws.quirk_ladder_offered_exact(L.explicit, rule, d, l):
  pq.quirk_ladder_offered_exact(L.explicit, rule, d, l)
