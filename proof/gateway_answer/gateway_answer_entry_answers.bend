# eukhe: the proof of LAW gateway_answer_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left
# (gateway_answer_entry_reads), so the entry answers the code's answer,
# with the laws' spelling (gaa.put: case by case).

import Base
import ../../bend/gateway_answer.bend as Ga
import ../../bend/ffi_gateway_answer.bend as FGa
import ../../bend/wire.bend as Wr
import ../../laws/gateway_answer.bend as GatewayAnswer
import ./gateway_answer_entry_reads.bend as PGatewayAnswerEntryReads

def gaa.put(a: Ga.Answer) -> {FGa.put_answer(a) == GatewayAnswer.ga_w_reply(a) : String}:
  match a:
    case Ga.ANone{}:
      {==}
    case Ga.AText{t}:
      {==}
    case Ga.AFailed{t}:
      {==}
    case Ga.AStopped{}:
      {==}

def GatewayAnswer.gateway_answer_entry_answers(ev, h):
  %Equal.sym(Wr.Dec<Ga.Ev>, FGa.get_req(GatewayAnswer.ga_w_req(ev, "")), Wr.Got{ev, ""}, GatewayAnswer.gateway_answer_entry_reads(ev, "", h)) : {FGa.ffi.got(_) == GatewayAnswer.ga_w_reply(Ga.answer(ev)) : String}
  gaa.put(Ga.answer(ev))
