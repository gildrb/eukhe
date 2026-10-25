# eukhe: the proof of LAW text_pat_hit
#
# PROOF: one pattern is the table of it alone, whose `or` with nothing is
# itself (LA.tpb.hit).

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA

def TextPat.text_pat_hit(s, p):
  LA.tpb.hit(s, p)
