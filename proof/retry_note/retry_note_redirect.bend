# eukhe: the proof of LAW retry_note_redirect
# The calls the code lists are the laws' listing (LARetryNote.rn.calls);
# then both texts compute to note.rs's fixed words around the fields.

import Base
import ../../bend/retry_note.bend as Rn
import ../../laws/retry_note.bend as RetryNote
import ./base.bend as LARetryNote

def rr.one(+a: Nat, +cs: List<&2, Rn.Call>, n: Nat, r: Nat, k: Nat) -> {Rn.text(a, Rn.Redirect{cs, n, r, k}) == RetryNote.opened(a, ["you made the same tool calls ", Nat.show(n), " times in a row, and they gave the same results each time: ", RetryNote.listed(cs), ". The harness did not run them again. Do not make these calls with these arguments again in this turn. Use different arguments, use a different tool, or give your answer with what you found. Redirect note ", Nat.show(r), " of ", Nat.show(k), "."]) : String}:
  %Equal.sym(String, String.join(RetryNote.shown_spec(cs), "; "), Rn.calls(cs), LARetryNote.rn.calls(cs)) : {Rn.text(a, Rn.Redirect{cs, n, r, k}) == RetryNote.opened(a, ["you made the same tool calls ", Nat.show(n), " times in a row, and they gave the same results each time: ", _, ". The harness did not run them again. Do not make these calls with these arguments again in this turn. Use different arguments, use a different tool, or give your answer with what you found. Redirect note ", Nat.show(r), " of ", Nat.show(k), "."]) : String}
  {==}

def RetryNote.retry_note_redirect(a, cs, n, r, k, cs2, n2, r2, k2):
  ("you made the same tool calls ", (" times in a row, and they gave the same results each time: ", (". The harness did not run them again. Do not make these calls with these arguments again in this turn. Use different arguments, use a different tool, or give your answer with what you found. Redirect note ", (" of ", (".", (rr.one(a, cs, n, r, k), rr.one(a, cs2, n2, r2, k2)))))))
