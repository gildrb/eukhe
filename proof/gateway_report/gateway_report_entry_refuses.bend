# eukhe: the proof of LAW gateway_report_entry_refuses
#
# PROOF: the entry answers either a step, which opens with a Nat (never
# 'E': wire_nat_not_err), or the one error form; so an answer that opens
# with 'E' is that error form.

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../bend/gateway_report.bend as Gr
import ../../bend/ffi_gateway_report.bend as FGr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_report.bend as GatewayReport
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def grf.put_ok(a: Ga.Answer, rest: String) -> {LawsBase.wire_opens_err(FGr.put_answer(a, rest)) == False{} : Bool}:
  match a:
    case Ga.ANone{}:
      Wire.wire_nat_not_err(0n, rest)
    case Ga.AText{t}:
      Wire.wire_nat_not_err(1n, Wr.put_str(t, rest))
    case Ga.AFailed{t}:
      Wire.wire_nat_not_err(2n, Wr.put_str(t, rest))
    case Ga.AStopped{}:
      Wire.wire_nat_not_err(3n, rest)

def grf.out_ok(o: Gr.Out) -> {LawsBase.wire_opens_err(FGr.put_out(o)) == False{} : Bool}:
  match o:
    case Gr.Out{h, s}:
      grf.put_ok(h, FGr.put_answer(s, ""))

def grf.done_ok(q: FGr.Req) -> {LawsBase.wire_opens_err(FGr.ffi.done(True{}, q)) == False{} : Bool}:
  match q:
    case FGr.Req{h, a, e}:
      grf.out_ok(Gr.step(h, a, e))

def grf.refuse(d: Wr.Dec<FGr.Req>, bad: {LawsBase.wire_opens_err(FGr.ffi.got(d)) == True{} : Bool}) -> {FGr.ffi.got(d) == Wr.err("gateway_report: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FGr.ffi.done(True{}, q) == Wr.err("gateway_report: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FGr.ffi.done(True{}, q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FGr.ffi.done(True{}, q)), True{}, bad), grf.done_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def GatewayReport.gateway_report_entry_refuses(s, bad):
  grf.refuse(FGr.get_req(s), bad)
