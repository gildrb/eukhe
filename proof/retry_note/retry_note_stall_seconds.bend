# eukhe: the proof of LAW retry_note_stall_seconds
# s * 1000 + rem ms with rem below 1000 is s whole seconds
# (LARetryNote.rn.div1000: divmod's loop counted out); then both texts
# compute to note.rs's fixed words around the seconds.

import Base
import ../../bend/retry_note.bend as Rn
import ../../laws/retry_note.bend as RetryNote
import ./base.bend as LARetryNote

def rst.one(+a: Nat, +s: Nat, +rem: Nat, +below: {Nat.is_lt(rem, 1000n) == True{} : Bool}) -> {Rn.text(a, Rn.Stalled{Nat.add(Nat.mul(s, 1000n), rem)}) == RetryNote.opened(a, ["your previous reply produced no output for ", Nat.show(s), " s, so the harness cut it. Reason briefly, then act: give the answer or call the tool of the next step."]) : String}:
  %LARetryNote.rn.div1000(s, rem, below) : {Rn.text(a, Rn.Stalled{Nat.add(Nat.mul(s, 1000n), rem)}) == RetryNote.opened(a, ["your previous reply produced no output for ", Nat.show(_), " s, so the harness cut it. Reason briefly, then act: give the answer or call the tool of the next step."]) : String}
  {==}

def RetryNote.retry_note_stall_seconds(a, s, rem, s2, rem2, below, below2):
  ("your previous reply produced no output for ", (" s, so the harness cut it. Reason briefly, then act: give the answer or call the tool of the next step.", (rst.one(a, s, rem, below), rst.one(a, s2, rem2, below2))))
