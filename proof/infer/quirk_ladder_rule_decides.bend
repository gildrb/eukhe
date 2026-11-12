# eukhe: the proof of LAW quirk_ladder_rule_decides

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ./quirk_ladder_explicit_decides/offers.bend as LD

def Infer.quirk_ladder_rule_decides(m, d, l):
  LD.ld.offers(m, If.Defaults.reasoning(d), l)
