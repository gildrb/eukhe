# eukhe: the proof of LAW phrase_any
#
# PROOF: by induction on the list; the lazy or is the Bool or (LA.phb.any).

import Base
import ../../bend/phrase.bend as P
import ../../laws/phrase.bend as Phrase
import ./base.bend as LA

def Phrase.phrase_any(s, phs):
  LA.phb.any(s, phs)
