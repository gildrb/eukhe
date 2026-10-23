# eukhe: the proof of LAW quirk_unknown_when_none

import Base
import ../../laws/infer.bend as Infer
import ./base.bend as LA

def Infer.quirk_unknown_when_none(rs, q, d, none):
  LA.pq.quirk_unknown_when_none(rs, q, d, none)
