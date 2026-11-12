# eukhe: the proof of LAW text_pat_fold
#
# PROOF: char by char, each answer of the code's three tests (capital,
# Kelvin sign, long s) is the CaseFolding.txt rows' answer; no code is both
# the Kelvin sign and the long s (LA.tpb.fold).

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA

def TextPat.text_pat_fold(s):
  LA.tpb.fold(s)
