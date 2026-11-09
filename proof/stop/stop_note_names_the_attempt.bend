# eukhe: the proof of LAW stop_note_names_the_attempt
#
# PROOF: the note is the attempt's prefix before the note's body, which reads no attempt.

import Base
import ../../bend/stop.bend as S
import ../../laws/stop.bend as Stop

def Stop.stop_note_names_the_attempt(n):
  (S.note.body(n), a => {==})
