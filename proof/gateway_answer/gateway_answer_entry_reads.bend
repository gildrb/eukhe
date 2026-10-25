# eukhe: the proof of LAW gateway_answer_entry_reads
#
# PROOF: tags, Bools and stops compute; a text reads back by
# wire_str_round_trip and the text blocks by the list round trip of the
# doc_commit entry (dcw.strs.rt; their lengths fit by the premise), so each
# stage of the decoder hands the next one exactly the rest after its
# field.

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../bend/ffi_gateway_answer.bend as FGa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire_strs.bend as LS
import ./base.bend as LA

def gar.maybe(m: Maybe<&2, String>, +rest: String, h: {GatewayAnswer.ga_fit_maybe(m) == True{} : Bool}) -> {FGa.get_maybe(Wr.get_nat(GatewayAnswer.ga_w_maybe(m, rest))) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, String>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {FGa.get_some(_) == Wr.Got{Some{x}, rest} : Wr.Dec<Maybe<&2, String>>}
      {==}

def gar.stop(s: Ga.Stop, -rest: String) -> {FGa.get_stop(Wr.get_nat(Wr.put_nat(GatewayAnswer.ga_w_stop(s), rest))) == Wr.Got{s, rest} : Wr.Dec<Ga.Stop>}:
  match s:
    case Ga.SStop{}:
      {==}
    case Ga.SLength{}:
      {==}
    case Ga.SError{}:
      {==}
    case Ga.SAborted{}:
      {==}
    case Ga.SToolUse{}:
      {==}

def gar.turn(a: Bool, e: Maybe<&2, String>, +rest: String, h: {GatewayAnswer.ga_fit_maybe(e) == True{} : Bool}) -> {FGa.get_turn(Wr.get_bool(Wr.put_bool(a, GatewayAnswer.ga_w_maybe(e, rest)))) == Wr.Got{Ga.ETurnEnd{a, e}, rest} : Wr.Dec<Ga.Ev>}:
  match a:
    case True{}:
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FGa.get_maybe(Wr.get_nat(GatewayAnswer.ga_w_maybe(e, rest))), Wr.Got{e, rest}, gar.maybe(e, rest, h)) : {FGa.get_turn.error(True{}, _) == Wr.Got{Ga.ETurnEnd{True{}, e}, rest} : Wr.Dec<Ga.Ev>}
      {==}
    case False{}:
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FGa.get_maybe(Wr.get_nat(GatewayAnswer.ga_w_maybe(e, rest))), Wr.Got{e, rest}, gar.maybe(e, rest, h)) : {FGa.get_turn.error(False{}, _) == Wr.Got{Ga.ETurnEnd{False{}, e}, rest} : Wr.Dec<Ga.Ev>}
      {==}

def gar.agent(a: Bool, -rest: String) -> {FGa.get_agent(Wr.get_bool(Wr.put_bool(a, rest))) == Wr.Got{Ga.EAgentEnd{a}, rest} : Wr.Dec<Ga.Ev>}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def gar.req(ev: Ga.Ev, +rest: String, h: {GatewayAnswer.ga_fit(ev) == True{} : Bool}) -> {FGa.get_req(GatewayAnswer.ga_w_req(ev, rest)) == Wr.Got{ev, rest} : Wr.Dec<Ga.Ev>}:
  match ev:
    case Ga.EAgentEnd{a}:
      gar.agent(a, rest)
    case Ga.EAssistant{+s, +ts, +e}:
      +hq = h
      +hr = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(List.length(&2, String, ts)), Bool.and(GatewayAnswer.ga_fit_strs(ts), GatewayAnswer.ga_fit_maybe(e)), hq)
      +fn = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(List.length(&2, String, ts)), Bool.and(GatewayAnswer.ga_fit_strs(ts), GatewayAnswer.ga_fit_maybe(e)), hq)
      +fd = Equal.trans(Bool, DocCommit.sp_fit_strs(ts), GatewayAnswer.ga_fit_strs(ts), True{}, Equal.sym(Bool, GatewayAnswer.ga_fit_strs(ts), DocCommit.sp_fit_strs(ts), LA.gab.fits(ts)), LLogicBool.tree.pt.and_l(GatewayAnswer.ga_fit_strs(ts), GatewayAnswer.ga_fit_maybe(e), hr))
      +fe = LLogicBool.tree.pt.and_r(GatewayAnswer.ga_fit_strs(ts), GatewayAnswer.ga_fit_maybe(e), hr)
      +m = GatewayAnswer.ga_w_maybe(e, rest)
      +l = Wr.put_list(~String, ~Wr.put_str, ts, m)
      %Equal.sym(Wr.Dec<Ga.Stop>, FGa.get_stop(Wr.get_nat(Wr.put_nat(GatewayAnswer.ga_w_stop(s), l))), Wr.Got{s, l}, gar.stop(s, l)) : {FGa.get_assistant(_) == Wr.Got{Ga.EAssistant{s, ts, e}, rest} : Wr.Dec<Ga.Ev>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, l), Wr.Got{ts, m}, LS.dcw.strs.rt(ts, m, fn, fd)) : {FGa.get_assistant.texts(s, _) == Wr.Got{Ga.EAssistant{s, ts, e}, rest} : Wr.Dec<Ga.Ev>}
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FGa.get_maybe(Wr.get_nat(m)), Wr.Got{e, rest}, gar.maybe(e, rest, fe)) : {FGa.get_assistant.error(s, ts, _) == Wr.Got{Ga.EAssistant{s, ts, e}, rest} : Wr.Dec<Ga.Ev>}
      {==}
    case Ga.ETurnEnd{a, e}:
      gar.turn(a, e, rest, h)
    case Ga.EOther{}:
      {==}

def GatewayAnswer.gateway_answer_entry_reads(ev, rest, h):
  gar.req(ev, rest, h)
