# eukhe: the proof of LAW search_open_answers: the request reads back whole and is
# six limits

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../bend/wire.bend as Wr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LADocSearch

def DocSearch.search_open_answers(p, s, k, rem, t, maxb, h):
  +xs = {[p, s, k, rem, t, maxb] : List<&2, Nat>}
  %LADocSearch.dsb.read(xs, h) : {FDs.open.got(_) == (FDs.Walk{p, s, k, rem, 0n, t, maxb}, "") : FDs.St & String}
  {==}
