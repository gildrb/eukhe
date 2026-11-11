# eukhe: the proof of LAW retry_note_opens_with_attempt
# The model's text is the opening, then the cause's body (Rn.body), the
# same for every attempt; the opening's list ends the body with "".

import Base
import ../../bend/retry_note.bend as Rn
import ../../laws/retry_note.bend as RetryNote
import ./base.bend as LARetryNote

def ow.one(+a: Nat, +c: Rn.Cause) -> {Rn.text(a, c) == RetryNote.opened(a, [Rn.body(c)]) : String}:
  Equal.cong(String, String, z => String.append("Harness note, attempt ", String.append(Nat.show(a), String.append(": ", z))), Rn.body(c), String.append(Rn.body(c), ""), Equal.sym(String, String.append(Rn.body(c), ""), Rn.body(c), LARetryNote.rn.append_nil(Rn.body(c))))

def RetryNote.retry_note_opens_with_attempt(a, b, c):
  (Rn.body(c), (ow.one(a, c), ow.one(b, c)))
