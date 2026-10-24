# eukhe: the proof of LAW limit_cuts: the two sums step alike

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LADocSearch

def DocSearch.limit_cuts(cs, l):
  %LADocSearch.ds.sum(cs) : {Nat.is_lt(l, Sr.sum(cs)) == Nat.is_lt(l, _) : Bool}
  {==}
