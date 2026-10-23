# eukhe: the proof of LAW quirk_ladder_rule_second

import Base
import ../../bend/effort.bend as Ef
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer

def pq.quirk_ladder_rule_second(+l: Ef.LvMap) -> {If.lad.chosen(None{}, Some{l}) == l : Ef.LvMap}:
  {==}

def Infer.quirk_ladder_rule_second(l):
  pq.quirk_ladder_rule_second(l)
