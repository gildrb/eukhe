# eukhe: the proof of LAW text_pat_class_table
#
# PROOF: class by class, the code's test computes to the test the table's
# rows spell (LA.tpb.cls).

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA

def TextPat.text_pat_class_table(k, x):
  LA.tpb.cls(k, x)
