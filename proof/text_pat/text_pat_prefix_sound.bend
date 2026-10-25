# eukhe: the proof of LAW text_pat_prefix_sound
#
# PROOF: every True answer of the code's prefix test comes with a prefix that
# matches (LA.tpb.sp, by induction as the test runs: a star's two ways
# each give their own part); the premise says the answer is True.

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA

def TextPat.text_pat_prefix_sound(s, its, h):
  %h : LA.tpb.SP(s, its, _)
  LA.tpb.sp(s, its)
