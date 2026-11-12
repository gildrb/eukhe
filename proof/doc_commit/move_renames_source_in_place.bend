# eukhe: the proof of LAW move_renames_source_in_place
#
# PROOF: a free destination takes the rename arm; the rename puts the file named as the source in its place under the destination name (dcl.renamed_at, dcl.put_src).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/doc_commit.bend as DocCommit
import ./base.bend as LA

def dcf.ren(h: Bool, +s: Nat, +t: Nat, +pre: List<&2, Cm.Entry>, +b: Nat, +post: List<&2, Cm.Entry>, free: {h == False{} : Bool}) -> {List.get(&2, Cm.Entry, Cm.Mv.es(Cm.move.go(s, t, h, List.append(&2, Cm.Entry, pre, Cm.Entry{s, b} <> post))), List.length(&2, Cm.Entry, pre)) == Some{Cm.Entry{t, b}} : Maybe<&2, Cm.Entry>}:
  match h:
    case True{}:
      LA.dcw.tf({List.get(&2, Cm.Entry, Cm.Mv.es(Cm.move.go(s, t, True{}, List.append(&2, Cm.Entry, pre, Cm.Entry{s, b} <> post))), List.length(&2, Cm.Entry, pre)) == Some{Cm.Entry{t, b}} : Maybe<&2, Cm.Entry>}, free)
    case False{}:
      LA.dcl.renamed_at(s, t, pre, s, b, post, Cm.Entry{t, b}, LA.dcl.put_src(t, s, b, Cm.rename(s, t, post), Nat.is_eq(s, s), LA.dcl.nat_refl(s)))

def DocCommit.move_renames_source_in_place(s, t, pre, b, post, free):
  dcf.ren(Cm.has(t, List.append(&2, Cm.Entry, pre, Cm.Entry{s, b} <> post)), s, t, pre, b, post, free)
