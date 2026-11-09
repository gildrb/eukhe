# eukhe: the proof of LAW quirk_ladder_explicit_decides

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ./quirk_ladder_explicit_decides/offers.bend as LD

def Infer.quirk_ladder_explicit_decides(e, rule, d, l):
  LD.ld.offers(e, If.Defaults.reasoning(d), l)
