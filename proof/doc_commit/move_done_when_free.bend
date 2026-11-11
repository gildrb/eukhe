# eukhe: the proof of LAW move_done_when_free
#
# PROOF: a free destination takes the rename arm, and a rename keeps the number of files (dcl.rename_len).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def dcf.done(b: Bool, +s: Nat, +t: Nat, +es: List<&2, Cm.Entry>, free: {b == False{} : Bool}) -> {Cm.Mv.ok(Cm.move.go(s, t, b, es)) == True{} : Bool} & {List.length(&2, Cm.Entry, Cm.Mv.es(Cm.move.go(s, t, b, es))) == List.length(&2, Cm.Entry, es) : Nat}:
  match b:
    case True{}:
      LA.dcw.tf({Cm.Mv.ok(Cm.move.go(s, t, True{}, es)) == True{} : Bool} & {List.length(&2, Cm.Entry, Cm.Mv.es(Cm.move.go(s, t, True{}, es))) == List.length(&2, Cm.Entry, es) : Nat}, free)
    case False{}:
      ({==}, LA.dcl.rename_len(s, t, es))

def DocCommit.move_done_when_free(s, t, es, free):
  dcf.done(Cm.has(t, es), s, t, es, free)
