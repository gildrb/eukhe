# eukhe: the proof of LAW text_pat_lower
#
# PROOF: char by char, each answer of the code's three tests (capital,
# Kelvin sign, capital I with dot) is the UnicodeData.txt and
# SpecialCasing.txt rows' answer; no code is two of them (LA.tpb.lower).

import Base
import ../../bend/text_pat.bend as Tp
import ../../laws/base.bend as LawsBase
import ../../laws/text_pat.bend as TextPat
import ./base.bend as LA

def TextPat.text_pat_lower(s):
  LA.tpb.lower(s)
