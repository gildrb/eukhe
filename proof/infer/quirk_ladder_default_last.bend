# eukhe: the proof of LAW quirk_ladder_default_last

import Base
import ../../bend/infer.bend as If
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws

def pq.quirk_ladder_default_last() -> {If.lad.chosen(None{}, None{}) == Ef.LvMap.none() : Ef.LvMap}:
  {==}

def Laws.quirk_ladder_default_last():
  pq.quirk_ladder_default_last()
