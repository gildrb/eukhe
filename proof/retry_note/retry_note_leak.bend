# eukhe: the proof of LAW retry_note_leak
# Both texts compute to note.rs's fixed words around the markup, the reason,
# the row and the cap.

import Base
import ../../bend/retry_note.bend as Rn
import ../../laws/retry_note.bend as RetryNote
import ./base.bend as LARetryNote

def RetryNote.retry_note_leak(a, m, why, r, k, m2, why2, r2, k2):
  ("your previous reply wrote a tool call as ", (" markup in its text, and the harness could not read it (", ("). No tool ran. Make the call again through the tool-calling interface, with its arguments as one JSON object that agrees with the schema of the tool. Do not write a tool call as text. If you need no tool, give the answer as plain text. Leak note ", (" of ", (".", ({==}, {==}))))))
