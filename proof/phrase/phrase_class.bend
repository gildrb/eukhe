# eukhe: the proof of LAW phrase_class
#
# PROOF: class by class (LA.phb.cls); COut by induction on its chars.

import Base
import ../../bend/phrase.bend as P
import ../../laws/phrase.bend as Phrase
import ./base.bend as LA

def Phrase.phrase_class(k, x):
  LA.phb.cls(k, x)
