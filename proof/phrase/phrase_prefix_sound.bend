# eukhe: the proof of LAW phrase_prefix_sound
#
# PROOF: by induction on the text and the items, as the prefix test runs
# (LA.phb.sp: a True answer of the code comes with its part and rest).

import Base
import ../../bend/phrase.bend as P
import ../../laws/phrase.bend as Phrase
import ./base.bend as LA

def Phrase.phrase_prefix_sound(s, its, end, h):
  %h : LA.phb.SP(s, its, end, _)
  LA.phb.sp(s, its, end)
