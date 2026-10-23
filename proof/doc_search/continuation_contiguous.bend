# eukhe: the proof of LAW continuation_contiguous

import Base
import ../../bend/doc_search.bend as Sr
import ../../LAWS.bend as Laws
import ./base.bend as LA

def ps.contig_at(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +c: Nat, e: {Nat.add(s, k) == c : Nat}) -> {List.append(&2, Nat, Sr.page(ps, s, k), List.append(&2, Nat, Sr.page(ps, c, k), List.drop(&2, Nat, List.drop(&2, Nat, ps, c), k))) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}:
  %e : {List.append(&2, Nat, Sr.page(ps, s, k), List.append(&2, Nat, Sr.page(ps, _, k), List.drop(&2, Nat, List.drop(&2, Nat, ps, _), k))) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}
  LA.ps.contig(ps, s, k)

# the law continuation_contiguous
def ps.contiguous(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +c: Nat, h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}) -> &rest: List<&2, Nat> -> {List.append(&2, Nat, Sr.page(ps, s, k), List.append(&2, Nat, Sr.page(ps, c, k), rest)) == List.drop(&2, Nat, ps, s) : List<&2, Nat>}:
  (List.drop(&2, Nat, List.drop(&2, Nat, ps, c), k), ps.contig_at(ps, s, k, c, LA.ps.next_c(ps, s, k, c, h)))

def Laws.continuation_contiguous(ps, s, k, c, h):
  ps.contiguous(ps, s, k, c, h)
