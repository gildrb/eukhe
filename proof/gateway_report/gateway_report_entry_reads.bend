# eukhe: the proof of LAW gateway_report_entry_reads
#
# PROOF: tags and Bools compute; a text reads back by wire_str_round_trip
# and a left text by gateway_answer's Maybe round trip (gar.maybe), so
# each stage of the decoder hands the next one exactly the rest after its
# field.

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../bend/gateway_report.bend as Gr
import ../../bend/ffi_gateway_answer.bend as FGa
import ../../bend/ffi_gateway_report.bend as FGr
import ../../bend/wire.bend as Wr
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/gateway_report.bend as GatewayReport
import ../../laws/wire.bend as Wire
import ../gateway_answer/base.bend as LA
import ../gateway_answer/gateway_answer_entry_reads.bend as PGar

def grr.answer(a: Ga.Answer, +rest: String, h: {GatewayReport.gr_fit_answer(a) == True{} : Bool}) -> {FGr.get_answer(Wr.get_nat(GatewayReport.gr_w_answer(a, rest))) == Wr.Got{a, rest} : Wr.Dec<Ga.Answer>}:
  match a:
    case Ga.ANone{}:
      {==}
    case Ga.AText{+t}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(t, rest)), Wr.Got{t, rest}, Wire.wire_str_round_trip(t, rest, h)) : {FGr.get_text(_) == Wr.Got{Ga.AText{t}, rest} : Wr.Dec<Ga.Answer>}
      {==}
    case Ga.AFailed{+t}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(t, rest)), Wr.Got{t, rest}, Wire.wire_str_round_trip(t, rest, h)) : {FGr.get_failed(_) == Wr.Got{Ga.AFailed{t}, rest} : Wr.Dec<Ga.Answer>}
      {==}
    case Ga.AStopped{}:
      {==}

def grr.run(w: Bool, +l: Maybe<&2, String>, +rest: String, +h: {GatewayAnswer.ga_fit_maybe(l) == True{} : Bool}) -> {FGr.get_run(Wr.get_bool(Wr.put_bool(w, GatewayAnswer.ga_w_maybe(l, rest)))) == Wr.Got{Gr.ERun{w, l}, rest} : Wr.Dec<Gr.End>}:
  match w:
    case True{}:
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FGa.get_maybe(Wr.get_nat(GatewayAnswer.ga_w_maybe(l, rest))), Wr.Got{l, rest}, PGar.gar.maybe(l, rest, h)) : {FGr.get_run.left(True{}, _) == Wr.Got{Gr.ERun{True{}, l}, rest} : Wr.Dec<Gr.End>}
      {==}
    case False{}:
      %Equal.sym(Wr.Dec<Maybe<&2, String>>, FGa.get_maybe(Wr.get_nat(GatewayAnswer.ga_w_maybe(l, rest))), Wr.Got{l, rest}, PGar.gar.maybe(l, rest, h)) : {FGr.get_run.left(False{}, _) == Wr.Got{Gr.ERun{False{}, l}, rest} : Wr.Dec<Gr.End>}
      {==}

def grr.end(e: Gr.End, +rest: String, h: {GatewayReport.gr_fit_end(e) == True{} : Bool}) -> {FGr.get_end(Wr.get_nat(GatewayReport.gr_w_end(e, rest))) == Wr.Got{e, rest} : Wr.Dec<Gr.End>}:
  match e:
    case Gr.ENone{}:
      {==}
    case Gr.ERun{w, l}:
      grr.run(w, l, rest, h)

def grr.req(q: FGr.Req, +rest: String, h: {GatewayReport.gr_fit(q) == True{} : Bool}) -> {FGr.get_req(GatewayReport.gr_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FGr.Req>}:
  match q:
    case FGr.Req{+hd, +a, +e}:
      +hq = h
      +f1 = LA.gab.and_l(GatewayReport.gr_fit_answer(hd), Bool.and(GatewayReport.gr_fit_answer(a), GatewayReport.gr_fit_end(e)), hq)
      +f23 = LA.gab.and_r(GatewayReport.gr_fit_answer(hd), Bool.and(GatewayReport.gr_fit_answer(a), GatewayReport.gr_fit_end(e)), hq)
      +f2 = LA.gab.and_l(GatewayReport.gr_fit_answer(a), GatewayReport.gr_fit_end(e), f23)
      +f3 = LA.gab.and_r(GatewayReport.gr_fit_answer(a), GatewayReport.gr_fit_end(e), f23)
      +m = GatewayReport.gr_w_end(e, rest)
      +n = GatewayReport.gr_w_answer(a, m)
      %Equal.sym(Wr.Dec<Ga.Answer>, FGr.get_answer(Wr.get_nat(GatewayReport.gr_w_answer(hd, n))), Wr.Got{hd, n}, grr.answer(hd, n, f1)) : {FGr.get_req.held(_) == Wr.Got{FGr.Req{hd, a, e}, rest} : Wr.Dec<FGr.Req>}
      %Equal.sym(Wr.Dec<Ga.Answer>, FGr.get_answer(Wr.get_nat(n)), Wr.Got{a, m}, grr.answer(a, m, f2)) : {FGr.get_req.answer(hd, _) == Wr.Got{FGr.Req{hd, a, e}, rest} : Wr.Dec<FGr.Req>}
      %Equal.sym(Wr.Dec<Gr.End>, FGr.get_end(Wr.get_nat(m)), Wr.Got{e, rest}, grr.end(e, rest, f3)) : {FGr.get_req.end(hd, a, _) == Wr.Got{FGr.Req{hd, a, e}, rest} : Wr.Dec<FGr.Req>}
      {==}

def GatewayReport.gateway_report_entry_reads(q, rest, h):
  grr.req(q, rest, h)
