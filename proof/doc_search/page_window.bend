# eukhe: the proof of LAW page_window
#
# PROOF: the page is take(drop(ps, s), k); what follows it, drop(ps, s +
# k), is drop(drop(ps, s), k) (ps.drop_drop); take then drop of a list is
# the list (ps.take_drop), twice. Its length: take keeps min(k, |xs|)
# items, drop leaves |ps| - s.

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LA

def pw.len_take(xs: List<&2, Nat>, k: Nat) -> {List.length(&2, Nat, List.take(&2, Nat, xs, k)) == Nat.min(k, List.length(&2, Nat, xs)) : Nat}:
  match xs k:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+q:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+q:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Nat, List.take(&2, Nat, t, q)), Nat.min(q, List.length(&2, Nat, t)), pw.len_take(t, q))

def pw.len_drop(xs: List<&2, Nat>, s: Nat) -> {List.length(&2, Nat, List.drop(&2, Nat, xs, s)) == Nat.sub(List.length(&2, Nat, xs), s) : Nat}:
  match xs s:
    case Nil{} s:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+q:
      pw.len_drop(t, q)

def pw.pieces(+ps: List<&2, Nat>, +s: Nat, +k: Nat) -> {List.append(&2, Nat, List.take(&2, Nat, ps, s), List.append(&2, Nat, Sr.page(ps, s, k), List.drop(&2, Nat, ps, Nat.add(s, k)))) == ps : List<&2, Nat>}:
  +d = List.drop(&2, Nat, ps, s)
  %LA.ps.drop_drop(ps, s, k) : {List.append(&2, Nat, List.take(&2, Nat, ps, s), List.append(&2, Nat, List.take(&2, Nat, d, k), _)) == ps : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, List.append(&2, Nat, List.take(&2, Nat, d, k), List.drop(&2, Nat, d, k)), d, LA.ps.take_drop(d, k)) : {List.append(&2, Nat, List.take(&2, Nat, ps, s), _) == ps : List<&2, Nat>}
  LA.ps.take_drop(ps, s)

def pw.len(+ps: List<&2, Nat>, +s: Nat, +k: Nat) -> {List.length(&2, Nat, Sr.page(ps, s, k)) == Nat.min(k, Nat.sub(List.length(&2, Nat, ps), s)) : Nat}:
  %pw.len_drop(ps, s) : {List.length(&2, Nat, Sr.page(ps, s, k)) == Nat.min(k, _) : Nat}
  pw.len_take(List.drop(&2, Nat, ps, s), k)

def DocSearch.page_window(ps, s, k):
  (pw.pieces(ps, s, k), pw.len(ps, s, k))
