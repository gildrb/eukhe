# eukhe: the proof of LAW next_is_more: the continuation is some exactly when the
# list after s + k is not empty

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def next.put_drop(ps: List<&2, Nat>, c: Nat, +v: Nat) -> {Sr.next.put(List.drop(&2, Nat, ps, c), v) == DocSearch.ds_some_if(Nat.is_lt(c, List.length(&2, Nat, ps)), v) : Maybe<&2, Nat>}:
  match ps c:
    case Nil{} 0n:
      {==}
    case Nil{} 1n+q:
      {==}
    case h <> t 0n:
      {==}
    case h <> t 1n+q:
      next.put_drop(t, q, v)

def DocSearch.next_is_more(ps, s, k):
  match k:
    case 0n:
      {==}
    case 1n+j:
      next.put_drop(ps, Nat.add(s, 1n+j), Nat.add(s, 1n+j))
