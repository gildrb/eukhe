# eukhe: the proof of LAW move_refused_when_taken
#
# PROOF: the destination is taken (dcl.has_at), so the move is refused with the files.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def dcf.refused(b: Bool, +s: Nat, +t: Nat, +es: List<&2, Cm.Entry>, taken: {b == True{} : Bool}) -> {Cm.move.go(s, t, b, es) == Cm.Mv{False{}, es} : Cm.Mv}:
  match b:
    case True{}:
      {==}
    case False{}:
      LA.dcw.ft({Cm.move.go(s, t, False{}, es) == Cm.Mv{False{}, es} : Cm.Mv}, taken)

def DocCommit.move_refused_when_taken(s, pre, t, b, post):
  dcf.refused(Cm.has(t, List.append(&2, Cm.Entry, pre, Cm.Entry{t, b} <> post)), s, t, List.append(&2, Cm.Entry, pre, Cm.Entry{t, b} <> post), LA.dcl.has_at(pre, t, b, post))
