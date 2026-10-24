# eukhe: the proof of LAW upto_counts: the two counts step alike

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

def upto.from(t: Nat, +i: Nat) -> {Sr.upto.go(t, i) == DocSearch.ds_from(t, i) : List<&2, Nat>}:
  match t:
    case 0n:
      {==}
    case 1n+u:
      %upto.from(u, 1n+i) : {i <> Sr.upto.go(u, 1n+i) == i <> _ : List<&2, Nat>}
      {==}

def DocSearch.upto_counts(t):
  upto.from(t, 0n)
