# eukhe: the proof of LAW search_met_answers: the event reads back whole and as the
# file's form; the reply's Nats are the spec's

import Base
import ../../bend/doc_search.bend as Sr
import ../../bend/ffi_doc_search.bend as FDs
import ../../bend/wire.bend as Wr
import ../../laws/doc_search.bend as DocSearch
import ./base.bend as LADocSearch

def DocSearch.search_met_answers(p, s, k, rem, n, t, maxb, f, h):
  +w = {FDs.Walk{p, s, k, rem, n, t, maxb} : FDs.St}
  +e = {Sr.Ent{0n, f} : Sr.Ent}
  +o = Sr.out(e, p, s, k, rem, n)
  +kp = Sr.kept(e, p, rem)
  +w2 = {FDs.Walk{p, s, k, Sr.left(e, p, rem), Sr.seen(e, rem, n), Nat.sub(t, 1n), maxb} : FDs.St}
  +xs = {DocSearch.ds_met(f) : List<&2, Nat>}
  %LADocSearch.dsb.read(xs, h) : {FDs.step.got(w, _) == (w2, DocSearch.ds_spell(DocSearch.ds_said(o, kp))) : FDs.St & String}
  %LADocSearch.dsb.met(f) : {FDs.step.ev(w, _) == (w2, DocSearch.ds_spell(DocSearch.ds_said(o, kp))) : FDs.St & String}
  Equal.cong(List<&2, Nat>, FDs.St & String, x => (w2, Wr.put_list(~Nat, ~Wr.put_nat, x, "")), FDs.step.met.nats(o, kp), DocSearch.ds_said(o, kp), LADocSearch.dsb.said(o, kp))
