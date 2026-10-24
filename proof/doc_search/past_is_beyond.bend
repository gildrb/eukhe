# eukhe: the proof of LAW past_is_beyond: the list after the skip is empty exactly
# when the skip is the length or more

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def past.drop(ps: List<&2, Nat>, s: Nat) -> {List.is_empty(&2, Nat, List.drop(&2, Nat, ps, s)) == Nat.is_le(List.length(&2, Nat, ps), s) : Bool}:
  match ps s:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+q:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+q:
      past.drop(t, q)

def DocSearch.past_is_beyond(ps, s):
  match ps:
    case Nil{}:
      {==}
    case h <> t:
      past.drop(h <> t, s)
