# eukhe: the proof of LAW afw_answers_spelled
#
# PROOF: the grammar's spelling is the entry's own encoding (LA.pfs.req),
# which reads back (afw_req_round_trip); with nothing left the entry
# answers the model's decision, encoded by its own encoders, which write
# what the grammar spells (pfs.answer: LA.pfs.gate, LA.pfs.route, and the
# events and keys of a pass, pfs.pass).

import Base
import ../../bend/aux_fallback.bend as Af
import ../../bend/ffi_aux_fallback.bend as FAf
import ../../bend/wire.bend as Wr
import ../../laws/aux_fallback.bend as AuxFallback
import ./base.bend as LA
import ./afw_evs_round_trip.bend as PAfwEvsRoundTrip

# the entry's event encoder writes what the grammar spells
def pfs.ev(e: Af.Ev, -rest: String) -> {FAf.put_ev(e, rest) == AuxFallback.afw_spell_ev(e, rest) : String}:
  match e:
    case Af.Stay{}:
      {==}
    case Af.Went{}:
      {==}
    case Af.Sub{k}:
      match k:
        case Af.K{p, s, q}:
          {==}
    case Af.Note{k}:
      match k:
        case Af.K{p, s, q}:
          {==}

def pfs.ev_items(xs: List<&2, Af.Ev>, -rest: String) -> {PAfwEvsRoundTrip.pfw.ev_items(xs, rest) == AuxFallback.afw_spell_ev_items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      %pfs.ev_items(t, rest) : {FAf.put_ev(x, PAfwEvsRoundTrip.pfw.ev_items(t, rest)) == AuxFallback.afw_spell_ev(x, _) : String}
      pfs.ev(x, PAfwEvsRoundTrip.pfw.ev_items(t, rest))

def pfs.evs(+xs: List<&2, Af.Ev>, -rest: String) -> {Wr.put_list(~Af.Ev, ~FAf.put_ev, xs, rest) == AuxFallback.afw_spell_evs(xs, rest) : String}:
  %pfs.ev_items(xs, rest) : {Wr.put_list(~Af.Ev, ~FAf.put_ev, xs, rest) == Wr.put_nat(List.length(&2, Af.Ev, xs), _) : String}
  PAfwEvsRoundTrip.pfw.ev_put(xs, rest)

# a pass's reply, the model's events then its keys, is their spelling
def pfs.pass(+r: Af.Route, +sh: List<&2, Af.Key>) -> {FAf.put_pass((Af.put(r, sh, Nil{}), Af.after(r, sh)), "") == AuxFallback.afw_spell_evs(Af.put(r, sh, Nil{}), AuxFallback.afw_spell_keys(Af.after(r, sh), "")) : String}:
  +es = Af.put(r, sh, Nil{})
  +ks = Af.after(r, sh)
  %LA.pfs.keys(ks, "") : {FAf.put_pass((es, ks), "") == AuxFallback.afw_spell_evs(es, _) : String}
  pfs.evs(es, Wr.put_list(~Af.Key, ~FAf.put_key, ks, ""))

# the entry's answer on a request is the spelled model decision
def pfs.answer(x: FAf.Req) -> {FAf.answer(x) == AuxFallback.afw_spell_answer(x) : String}:
  match x:
    case FAf.GateReq{p, sel, ok}:
      LA.pfs.gate(Af.gate(p, sel, ok), "")
    case FAf.SettleReq{g, look, need}:
      LA.pfs.route(Af.settle(g, look, need), "")
    case FAf.PassReq{+r, +sh}:
      pfs.pass(r, sh)

def AuxFallback.afw_answers_spelled(x, fits):
  Equal.trans(String, FAf.ffi(AuxFallback.afw_spell_req(x, "")), FAf.answer(x), AuxFallback.afw_spell_answer(x), LA.pfs.run(x, "", fits), pfs.answer(x))
