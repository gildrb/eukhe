# eukhe: the proof of LAW quirk_ladder_explicit_first

import Base
import ../../bend/infer.bend as If
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws

# The thinking ladder
# -------------------

def pq.quirk_ladder_explicit_first(+e: Ef.LvMap, +rule: Maybe<&2, Ef.LvMap>) -> {If.lad.chosen(Some{e}, rule) == e : Ef.LvMap}:
  {==}

def Laws.quirk_ladder_explicit_first(e, rule):
  pq.quirk_ladder_explicit_first(e, rule)
