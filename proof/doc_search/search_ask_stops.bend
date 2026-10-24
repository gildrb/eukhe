# eukhe: the proof of LAW search_ask_stops: the ask reads back whole, its ranges read
# back, and no match is left

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../bend/wire.bend as Wr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LADocSearch

def DocSearch.search_ask_stops(p, s, k, n, t, maxb, rs, h):
  +w = {FDs.Walk{p, s, k, 0n, n, t, maxb} : FDs.St}
  +xs = {DocSearch.ds_ask(rs) : List<&2, Nat>}
  %LADocSearch.dsb.read(xs, h) : {FDs.step.got(w, _) == (w, DocSearch.ds_spell([0n, t])) : FDs.St & String}
  %LADocSearch.dsb.ranges(rs) : {FDs.step.ev(w, FDs.ev.ask(_)) == (w, DocSearch.ds_spell([0n, t])) : FDs.St & String}
  {==}
