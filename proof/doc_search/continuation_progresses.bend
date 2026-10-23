# eukhe: the proof of LAW continuation_progresses

import Base
import ../../bend/doc_search.bend as Sr
import ../../LAWS.bend as Laws
import ./base.bend as LA

# the page of a continuation is not empty
def ps.prog_go(+ps: List<&2, Nat>, -c0: Nat, +j: Nat, after: List<&2, Nat>, e: {List.drop(&2, Nat, ps, c0) == after : List<&2, Nat>}, -c: Nat, h: {Sr.next.put(after, c0) == Some{c} : Maybe<&2, Nat>}) -> {List.is_empty(&2, Nat, Sr.page(ps, c, 1n+j)) == False{} : Bool}:
  match after:
    case Nil{}:
      LA.documents.ps.none_some({List.is_empty(&2, Nat, Sr.page(ps, c, 1n+j)) == False{} : Bool}, c, h)
    case x <> t:
      %LA.ps.some_inj(c0, c, h) : {List.is_empty(&2, Nat, Sr.page(ps, _, 1n+j)) == False{} : Bool}
      %Equal.sym(List<&2, Nat>, List.drop(&2, Nat, ps, c0), x <> t, e) : {List.is_empty(&2, Nat, List.take(&2, Nat, _, 1n+j)) == False{} : Bool}
      {==}

# the law continuation_progresses
def ps.progresses(+ps: List<&2, Nat>, +s: Nat, +k: Nat, +c: Nat, h: {Sr.next(ps, s, k) == Some{c} : Maybe<&2, Nat>}) -> {List.is_empty(&2, Nat, Sr.page(ps, c, k)) == False{} : Bool}:
  match k:
    case 0n:
      LA.documents.ps.none_some({List.is_empty(&2, Nat, Sr.page(ps, c, 0n)) == False{} : Bool}, c, h)
    case 1n+j:
      ps.prog_go(ps, Nat.add(s, 1n+j), j, List.drop(&2, Nat, ps, Nat.add(s, 1n+j)), {==}, c, h)

# (F7) Continuations

def Laws.continuation_progresses(ps, s, k, c, h):
  ps.progresses(ps, s, k, c, h)
