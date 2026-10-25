# eukhe: the proof of LAW text_pat_class
#
# PROOF: the code's class test is the spec's, class by class (LA.tpb.cls).

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA

def TextPat.text_pat_class(k, x):
  LA.tpb.cls(k, x)
