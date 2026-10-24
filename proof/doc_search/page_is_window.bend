# eukhe: the proof of LAW page_is_window: drop then take is the spec's walk
# to the page

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

# take is the spec's first k
def page.first(ps: List<&2, Nat>, k: Nat) -> {List.take(&2, Nat, ps, k) == DocSearch.ds_first(ps, k) : List<&2, Nat>}:
  match ps k:
    case Nil{} k:
      {==}
    case h <> t 0n:
      {==}
    case +h <> t 1n+j:
      %page.first(t, j) : {h <> List.take(&2, Nat, t, j) == h <> _ : List<&2, Nat>}
      {==}

def page.window(ps: List<&2, Nat>, s: Nat, +k: Nat) -> {List.take(&2, Nat, List.drop(&2, Nat, ps, s), k) == DocSearch.ds_window(ps, s, k) : List<&2, Nat>}:
  match ps s:
    case Nil{} s:
      {==}
    case h <> t 0n:
      page.first(h <> t, k)
    case h <> t 1n+r:
      page.window(t, r, k)

def DocSearch.page_is_window(ps, s, k):
  page.window(ps, s, k)
