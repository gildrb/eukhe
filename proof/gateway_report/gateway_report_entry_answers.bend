# eukhe: the proof of LAW gateway_report_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (gateway_report_entry_reads), so the entry answers the code's step,
# with the laws' spelling (gra.put: case by case).

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../bend/gateway_report.bend as Gr
import ../../bend/ffi_gateway_report.bend as FGr
import ../../bend/wire.bend as Wr
import ../../laws/gateway_report.bend as GatewayReport
import ./gateway_report_entry_reads.bend as PGatewayReportEntryReads

def gra.put(a: Ga.Answer, rest: String) -> {FGr.put_answer(a, rest) == GatewayReport.gr_w_answer(a, rest) : String}:
  match a:
    case Ga.ANone{}:
      {==}
    case Ga.AText{t}:
      {==}
    case Ga.AFailed{t}:
      {==}
    case Ga.AStopped{}:
      {==}

def gra.out(o: Gr.Out) -> {FGr.put_out(o) == GatewayReport.gr_w_reply(o) : String}:
  match o:
    case Gr.Out{+h, +s}:
      %Equal.sym(String, FGr.put_answer(s, ""), GatewayReport.gr_w_answer(s, ""), gra.put(s, "")) : {FGr.put_answer(h, _) == GatewayReport.gr_w_reply(Gr.Out{h, s}) : String}
      gra.put(h, GatewayReport.gr_w_answer(s, ""))

def gra.done(q: FGr.Req) -> {FGr.ffi.done(True{}, q) == GatewayReport.gr_w_reply(GatewayReport.gr_step(q)) : String}:
  match q:
    case FGr.Req{h, a, e}:
      gra.out(Gr.step(h, a, e))

def GatewayReport.gateway_report_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FGr.Req>, FGr.get_req(GatewayReport.gr_w_req(q, "")), Wr.Got{q, ""}, GatewayReport.gateway_report_entry_reads(q, "", h)) : {FGr.ffi.got(_) == GatewayReport.gr_w_reply(GatewayReport.gr_step(q)) : String}
  gra.done(q)
