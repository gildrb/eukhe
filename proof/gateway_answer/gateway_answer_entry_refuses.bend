# eukhe: the proof of LAW gateway_answer_entry_refuses
#
# PROOF: the entry answers either an answer, which opens with a Nat (never
# 'E': wire_nat_not_err), or the one error form; so an answer that opens
# with 'E' is that error form.

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../bend/ffi_gateway_answer.bend as FGa
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_answer.bend as GatewayAnswer
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg

def gaf.put_ok(a: Ga.Answer) -> {LawsBase.wire_opens_err(FGa.put_answer(a)) == False{} : Bool}:
  match a:
    case Ga.ANone{}:
      Wire.wire_nat_not_err(0n, "")
    case Ga.AText{t}:
      Wire.wire_nat_not_err(1n, Wr.put_str(t, ""))
    case Ga.AFailed{t}:
      Wire.wire_nat_not_err(2n, Wr.put_str(t, ""))
    case Ga.AStopped{}:
      Wire.wire_nat_not_err(3n, "")

def gaf.refuse(d: Wr.Dec<Ga.Ev>, bad: {LawsBase.wire_opens_err(FGa.ffi.got(d)) == True{} : Bool}) -> {FGa.ffi.got(d) == Wr.err("gateway_answer: malformed request") : String}:
  match d:
    case Wr.Got{+ev, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FGa.put_answer(Ga.answer(ev)) == Wr.err("gateway_answer: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FGa.put_answer(Ga.answer(ev))), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FGa.put_answer(Ga.answer(ev))), True{}, bad), gaf.put_ok(Ga.answer(ev))))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def GatewayAnswer.gateway_answer_entry_refuses(s, bad):
  gaf.refuse(FGa.get_req(s), bad)
