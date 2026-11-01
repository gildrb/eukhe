# eukhe: the proof of LAW stop_note_exact
#
# PROOF: per note, both sides compute to the same text once the limit is split (LA.stb.note_text).

import Base
import ../../bend/stop.bend as S
import ./base.bend as LA
import ../../laws/stop.bend as Stop

def Stop.stop_note_exact(a, n):
  LA.stb.note_text(a, n)
