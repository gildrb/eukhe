# eukhe: the proof of LAW text_pat_any_sound
#
# PROOF: by induction on the patterns as the code tries them (LA.tpb.asd): a
# True answer comes from the first pattern the code finds, which names a
# found alternative (LA.tpb.hs); the premise says the answer is True.

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA

def TextPat.text_pat_any_sound(s, ps, h):
  %h : LA.tpb.AS(s, ps, _)
  LA.tpb.asd(s, ps)
