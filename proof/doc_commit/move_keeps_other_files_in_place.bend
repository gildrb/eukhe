# eukhe: the proof of LAW move_keeps_other_files_in_place
#
# PROOF: a free destination takes the rename arm; the rename keeps a file with another name in its place (dcl.renamed_at, dcl.put_other).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def dcf.keep(h: Bool, +s: Nat, +t: Nat, +pre: List<&2, Cm.Entry>, +m: Nat, +b: Nat, +post: List<&2, Cm.Entry>, free: {h == False{} : Bool}, other: {Nat.is_eq(m, s) == False{} : Bool}) -> {List.get(&2, Cm.Entry, Cm.Mv.es(Cm.move.go(s, t, h, List.append(&2, Cm.Entry, pre, Cm.Entry{m, b} <> post))), List.length(&2, Cm.Entry, pre)) == Some{Cm.Entry{m, b}} : Maybe<&2, Cm.Entry>}:
  match h:
    case True{}:
      LA.dcw.tf({List.get(&2, Cm.Entry, Cm.Mv.es(Cm.move.go(s, t, True{}, List.append(&2, Cm.Entry, pre, Cm.Entry{m, b} <> post))), List.length(&2, Cm.Entry, pre)) == Some{Cm.Entry{m, b}} : Maybe<&2, Cm.Entry>}, free)
    case False{}:
      LA.dcl.renamed_at(s, t, pre, m, b, post, Cm.Entry{m, b}, LA.dcl.put_other(t, m, b, Cm.rename(s, t, post), Nat.is_eq(m, s), other))

def DocCommit.move_keeps_other_files_in_place(s, t, pre, m, b, post, free, other):
  dcf.keep(Cm.has(t, List.append(&2, Cm.Entry, pre, Cm.Entry{m, b} <> post)), s, t, pre, m, b, post, free, other)
