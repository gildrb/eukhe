# eukhe: the proof of LAW retry_note_line
# The fixed words are note.rs's; both texts compute to them around the line.

import Base
import ../../bend/retry_note.bend as Rn
import ../../laws/retry_note.bend as RetryNote
import ./base.bend as LARetryNote

def RetryNote.retry_note_line(a, l, l2):
  ("your previous reply repeated the line ", (" until it was cut. Give the answer again; never list the same item twice.", ({==}, {==})))
