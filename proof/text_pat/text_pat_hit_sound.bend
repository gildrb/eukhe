# eukhe: the proof of LAW text_pat_hit_sound
#
# PROOF: by induction on the alternatives as the code tries them
# (LA.tpb.hs): a True answer comes from the first alternative the code finds,
# whose prefix test or search names its matching part (LA.tpb.fs, from the
# soundness of the prefix test and of the search); the premise says the
# answer is True.

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA

def TextPat.text_pat_hit_sound(s, a, alts, h):
  %h : LA.tpb.HS(a, s, alts, _)
  LA.tpb.hs(a, s, alts)
