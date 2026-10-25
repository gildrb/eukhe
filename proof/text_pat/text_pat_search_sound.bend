# eukhe: the proof of LAW text_pat_search_sound
#
# PROOF: a True answer of the search is a True answer of the prefix test at some
# suffix, which comes with its part (LA.tpb.os, from LA.tpb.sp).

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA

def TextPat.text_pat_search_sound(s, its, h):
  %h : LA.tpb.OSP(s, its, _)
  LA.tpb.os(s, its)
