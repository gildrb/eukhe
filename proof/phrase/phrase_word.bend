# eukhe: the proof of LAW phrase_word
#
# PROOF: both compute the same ranges on the char's code (LA.phb.word).

import Base
import ../../bend/phrase.bend as P
import ../../laws/phrase.bend as Phrase
import ./base.bend as LA

def Phrase.phrase_word(x):
  LA.phb.word(x)
