# eukhe: the proof of LAW text_pat_any
#
# PROOF: alternative by alternative and pattern by pattern, the lazy `or` of the
# code is the spec's Bool `or` (LA.tpb.any).

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA

def TextPat.text_pat_any(s, ps):
  LA.tpb.any(s, ps)
