# eukhe: the proof of LAW text_pat_prefix_complete
#
# PROOF: the code's prefix test is True for every text whose spec answer is True
# (LA.tpb.cp, by induction on the text, then the items, as the test runs);
# the premise says the spec answers True.

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA

def TextPat.text_pat_prefix_complete(u, its, rest, h):
  %h : LA.tpb.CP(u, its, rest, _)
  LA.tpb.cp(u, its, rest)
