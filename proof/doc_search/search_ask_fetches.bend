# eukhe: the proof of LAW search_ask_fetches: the ask reads back whole, its ranges read
# back, and a match is left

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../bend/wire.bend as Wr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LADocSearch

def DocSearch.search_ask_fetches(p, s, k, r, n, t, maxb, rs, h):
  +w = {FDs.Walk{p, s, k, 1n+r, n, t, maxb} : FDs.St}
  +xs = {DocSearch.ds_ask(rs) : List<&2, Nat>}
  +said = DocSearch.ds_spell([1n, Sr.fetch(rs, p, 1n+r, maxb)])
  %LADocSearch.dsb.read(xs, h) : {FDs.step.got(w, _) == (w, said) : FDs.St & String}
  %LADocSearch.dsb.ranges(rs) : {FDs.step.ev(w, FDs.ev.ask(_)) == (w, said) : FDs.St & String}
  {==}
