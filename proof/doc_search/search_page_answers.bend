# eukhe: the proof of LAW search_page_answers: the request reads back whole (the wire's
# list round trip), its multi bit reads back, and the reply's Nats are the
# spec's

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../bend/wire.bend as Wr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LADocSearch

def page.reply(+m: Bool, +ps: List<&2, Nat>, +s: Nat, +k: Nat) -> {FDs.answer.page(ps, s, k, m) == DocSearch.ds_opt(Sr.grep.next(m, ps, s, k)) <> DocSearch.ds_bit(Sr.grep.past(m, ps, s)) <> Sr.page(ps, s, k) : List<&2, Nat>}:
  +x = Sr.grep.next(m, ps, s, k)
  +y = Sr.grep.past(m, ps, s)
  %LADocSearch.dsb.maybn(x) : {FDs.maybn(x) <> FDs.bitn(y) <> Sr.page(ps, s, k) == _ <> DocSearch.ds_bit(y) <> Sr.page(ps, s, k) : List<&2, Nat>}
  %LADocSearch.dsb.bitn(y) : {FDs.maybn(x) <> FDs.bitn(y) <> Sr.page(ps, s, k) == FDs.maybn(x) <> _ <> Sr.page(ps, s, k) : List<&2, Nat>}
  {==}

def DocSearch.search_page_answers(t, s, k, m, h):
  +xs = {[0n, t, s, k, DocSearch.ds_bit(m)] : List<&2, Nat>}
  +ans = {DocSearch.ds_opt(Sr.grep.next(m, Sr.upto(t), s, k)) <> DocSearch.ds_bit(Sr.grep.past(m, Sr.upto(t), s)) <> Sr.page(Sr.upto(t), s, k) : List<&2, Nat>}
  %LADocSearch.dsb.read(xs, h) : {FDs.ffi.got(_) == DocSearch.ds_spell(ans) : String}
  %LADocSearch.dsb.bit_of(m) : {FDs.ffi.ask(FDs.req.page(t, s, k, _)) == DocSearch.ds_spell(ans) : String}
  Equal.cong(List<&2, Nat>, String, x => Wr.put_list(~Nat, ~Wr.put_nat, x, ""), FDs.answer.page(Sr.upto(t), s, k, m), ans, page.reply(m, Sr.upto(t), s, k))
