# eukhe: the proof of LAW phrase_prefix_complete
#
# PROOF: by induction on the part and the items, as the prefix test runs
# (LA.phb.cp: whatever the spec answers, a True answer passes).

import Base
import ../../bend/phrase.bend as P
import ../../laws/phrase.bend as Phrase
import ./base.bend as LA

def Phrase.phrase_prefix_complete(u, its, rest, end, h, he):
  %h : LA.phb.CP(u, its, rest, end, _)
  LA.phb.cp(u, its, rest, end, he)
