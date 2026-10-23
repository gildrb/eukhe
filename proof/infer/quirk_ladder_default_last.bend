# eukhe: the proof of LAW quirk_ladder_default_last

import Base
import ../../bend/effort.bend as Ef
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer

def pq.quirk_ladder_default_last() -> {If.lad.chosen(None{}, None{}) == Ef.LvMap.none() : Ef.LvMap}:
  {==}

def Infer.quirk_ladder_default_last():
  pq.quirk_ladder_default_last()
