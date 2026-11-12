# eukhe: the proof of LAW retry_note_cycle
# A period of 0 or of 2 or more is a cycle (1 is excluded by the premise);
# both texts compute to the cycle's fixed words around the count and line.

import Base
import ../../bend/retry_note.bend as Rn
import ../../laws/retry_note.bend as RetryNote
import ./base.bend as LARetryNote

def rc.one(+a: Nat, p: Nat, l: String, many: {Nat.is_eq(p, 1n) == False{} : Bool}) -> {Rn.text(a, Rn.Repeated{p, l}) == RetryNote.opened(a, ["your previous reply repeated a cycle of ", Nat.show(p), " lines, ending with the line ", l, ", until it was cut. Give the answer again; never repeat the same lines."]) : String}:
  match p:
    case 0n:
      {==}
    case 1n:
      LARetryNote.rn.absurd_t({Rn.text(a, Rn.Repeated{1n, l}) == RetryNote.opened(a, ["your previous reply repeated a cycle of ", Nat.show(1n), " lines, ending with the line ", l, ", until it was cut. Give the answer again; never repeat the same lines."]) : String}, many)
    case 2n+q:
      {==}

def RetryNote.retry_note_cycle(a, p, l, p2, l2, many, many2):
  ("your previous reply repeated a cycle of ", (" lines, ending with the line ", (", until it was cut. Give the answer again; never repeat the same lines.", (rc.one(a, p, l, many), rc.one(a, p2, l2, many2)))))
