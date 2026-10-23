# eukhe: the proof of LAW quirk_ladder_rule_second

import Base
import ../../bend/infer.bend as If
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws

def pq.quirk_ladder_rule_second(+l: Ef.LvMap) -> {If.lad.chosen(None{}, Some{l}) == l : Ef.LvMap}:
  {==}

def Laws.quirk_ladder_rule_second(l):
  pq.quirk_ladder_rule_second(l)
