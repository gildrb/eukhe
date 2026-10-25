# eukhe: the proof of LAW phrase_search_sound
#
# PROOF: a True answer of the search from the flag True is a True prefix
# test at some suffix, after a text whose flag is True (LA.phb.os); that
# flag is the spec's start edge (LA.phb.start, in LA.phb.os_fin).

import Base
import ../../bend/phrase.bend as P
import ../../laws/phrase.bend as Phrase
import ./base.bend as LA

def Phrase.phrase_search_sound(s, st, its, en, h):
  %h : LA.phb.SSP(s, st, its, en, _)
  LA.phb.os_fin(s, st, its, en, P.found(s, P.Ph{st, its, en}), LA.phb.os(s, st, its, en, True{}))
