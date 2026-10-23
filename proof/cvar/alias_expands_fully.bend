# eukhe: the proof of LAW alias_expands_fully

import Base
import ../../bend/cvar.bend as Cv
import ../../LAWS.bend as Laws
import ./base.bend as LA

def Laws.alias_expands_fully(cs, as):
  LA.pv.expand_plain(1n+List.length(&2, Cv.Alias, as), cs, as)
