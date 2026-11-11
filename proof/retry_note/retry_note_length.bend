# eukhe: the proof of LAW retry_note_length
# No reported limit computes to "the output limit"; a reported one is "the ",
# its number, "-token output limit", moved in front of the rest of the text
# (LARetryNote.rn.lim, associativity).

import Base
import ../../bend/retry_note.bend as Rn
import ../../laws/retry_note.bend as RetryNote
import ./base.bend as LARetryNote

def rl.two(+a: Nat, +t: Nat, r2: Nat, k2: Nat) -> {Rn.text(a, Rn.Length{1n+t, r2, k2}) == RetryNote.opened(a, ["your previous reply hit ", "the ", Nat.show(1n+t), "-token output limit", " while still reasoning, so the harness discarded it unseen, with every tool call it planned. Reason only about the next step, then call its tool. For a large deliverable (a file, a document, a long answer), write a minimal working version now and extend it in later turns. Length note ", Nat.show(r2), " of ", Nat.show(k2), "."]) : String}:
  +rest = String.concat([" while still reasoning, so the harness discarded it unseen, with every tool call it planned. Reason only about the next step, then call its tool. For a large deliverable (a file, a document, a long answer), write a minimal working version now and extend it in later turns. Length note ", Nat.show(r2), " of ", Nat.show(k2), "."])
  Equal.cong(String, String, z => String.append("Harness note, attempt ", String.append(Nat.show(a), String.append(": ", String.append("your previous reply hit ", z)))), String.append(Rn.limit(1n+t), rest), String.append("the ", String.append(Nat.show(1n+t), String.append("-token output limit", rest))), LARetryNote.rn.lim(t, rest))

def RetryNote.retry_note_length(a, t, r, k, r2, k2):
  ("your previous reply hit ", (" while still reasoning, so the harness discarded it unseen, with every tool call it planned. Reason only about the next step, then call its tool. For a large deliverable (a file, a document, a long answer), write a minimal working version now and extend it in later turns. Length note ", (" of ", (".", ({==}, rl.two(a, t, r2, k2))))))
