# eukhe: the proof of LAW text_pat_lower
#
# PROOF: char by char, the code's choice is the spec's in each of the cases of its
# three tests (LA.tpb.lower).

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA

def TextPat.text_pat_lower(s):
  LA.tpb.lower(s)
