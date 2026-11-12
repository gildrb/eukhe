# eukhe: the proof of LAW upto_numbers
#
# PROOF: the numbers from i, t of them, are t long and hold j + i at
# index j < t (by induction on t and j); from 0, j + 0 is j.

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LA

def un.len(t: Nat, +i: Nat) -> {List.length(&2, Nat, Sr.upto.go(t, i)) == t : Nat}:
  match t:
    case 0n:
      {==}
    case 1n+u:
      Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Nat, Sr.upto.go(u, 1n+i)), u, un.len(u, 1n+i))

def un.get(t: Nat, +i: Nat, j: Nat, h: {Nat.is_lt(j, t) == True{} : Bool}) -> {List.get(&2, Nat, Sr.upto.go(t, i), j) == Some{Nat.add(j, i)} : Maybe<&2, Nat>}:
  match t j:
    case 0n 0n:
      LA.ds.ft({List.get(&2, Nat, Sr.upto.go(0n, i), 0n) == Some{i} : Maybe<&2, Nat>}, h)
    case 0n 1n+q:
      LA.ds.ft({List.get(&2, Nat, Sr.upto.go(0n, i), 1n+q) == Some{1n+Nat.add(q, i)} : Maybe<&2, Nat>}, h)
    case 1n+u 0n:
      {==}
    case 1n+u 1n++q:
      %LA.ds.add_succ(q, i) : {List.get(&2, Nat, Sr.upto.go(u, 1n+i), q) == Some{_} : Maybe<&2, Nat>}
      un.get(u, 1n+i, q, h)

def DocSearch.upto_numbers(t, j, h):
  %LA.ds.add_zero(j) : {(List.length(&2, Nat, Sr.upto(t)), List.get(&2, Nat, Sr.upto(t), j)) == (t, Some{_}) : Nat & Maybe<&2, Nat>}
  %Equal.sym(Nat, List.length(&2, Nat, Sr.upto(t)), t, un.len(t, 0n)) : {(_, List.get(&2, Nat, Sr.upto(t), j)) == (t, Some{Nat.add(j, 0n)}) : Nat & Maybe<&2, Nat>}
  %Equal.sym(Maybe<&2, Nat>, List.get(&2, Nat, Sr.upto(t), j), Some{Nat.add(j, 0n)}, un.get(t, 0n, j, h)) : {(t, _) == (t, Some{Nat.add(j, 0n)}) : Nat & Maybe<&2, Nat>}
  {==}
