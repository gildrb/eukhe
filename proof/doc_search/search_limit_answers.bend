# eukhe: the proof of LAW search_limit_answers: the request reads back whole, and the
# cut bit is the spec's

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../bend/wire.bend as Wr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LADocSearch

def DocSearch.search_limit_answers(l, cs, h):
  +xs = {1n <> l <> cs : List<&2, Nat>}
  +ans = {DocSearch.ds_bit(Sr.rr.cut(cs, l)) <> Sr.rr(cs, l) : List<&2, Nat>}
  %LADocSearch.dsb.read(xs, h) : {FDs.ffi.got(_) == DocSearch.ds_spell(ans) : String}
  %LADocSearch.dsb.bitn(Sr.rr.cut(cs, l)) : {Wr.put_list(~Nat, ~Wr.put_nat, FDs.bitn(Sr.rr.cut(cs, l)) <> Sr.rr(cs, l), "") == Wr.put_list(~Nat, ~Wr.put_nat, _ <> Sr.rr(cs, l), "") : String}
  {==}
