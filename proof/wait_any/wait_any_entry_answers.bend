# eukhe: the proof of LAW wait_any_entry_answers
#
# PROOF: the entry's decoder is the laws' reader (wa.req), which reads the spelled request back whole with nothing left (wa.req_rt), so the entry answers the model's decision, which is the spec's (wait_any_poll_spec, wait_any_step_spec, wait_any_timeout_spec), spelled as the spec spells it.

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ./base.bend as LW
import ../../bend/ffi_wait_any.bend as FWa
import ../../bend/wire.bend as Wr
import ../../spec/durable/wait_any_wire.bend as SpW
import ./wait_any_poll_spec.bend as PWaitAnyPollSpec
import ./wait_any_step_spec.bend as PWaitAnyStepSpec
import ./wait_any_timeout_spec.bend as PWaitAnyTimeoutSpec

def wa.put_pick(p: Wa.Pick) -> {FWa.put_pick(p) == SpW.w_pick(p) : String}:
  match p:
    case Wa.Waits{}:
      {==}
    case Wa.Takes{i}:
      {==}
    case Wa.NoWork{}:
      {==}
    case Wa.Capped{}:
      {==}
    case Wa.Stopped{}:
      {==}

def wa.put_out(o: Wa.Out) -> {FWa.put_step(o) == SpW.w_out(o) : String}:
  match o:
    case Wa.Out{d, k}:
      match d:
        case Wa.D{w, p}:
          match p:
            case Wa.Live{}:
              {==}
            case Wa.Kept{}:
              {==}
            case Wa.Sent{}:
              {==}

# the entry's answer to a request is the spec's, spelled
def wa.answer(q: FWa.Req) -> {FWa.answer(q) == SpW.w_reply(q) : String}:
  match q:
    case FWa.QPoll{+n, +c, +l, +ts}:
      %WaitAny.wait_any_poll_spec(n, c, l, ts) : {FWa.put_pick(Wa.poll(n, c, l, ts)) == SpW.w_pick(_) : String}
      wa.put_pick(Wa.poll(n, c, l, ts))
    case FWa.QStep{+k, +d, +e}:
      %WaitAny.wait_any_step_spec(k, d, e) : {FWa.put_step(Wa.step(k, d, e)) == SpW.w_out(_) : String}
      wa.put_out(Wa.step(k, d, e))
    case FWa.QTimeout{+a}:
      %WaitAny.wait_any_timeout_spec(a) : {Wr.put_nat(Wa.timeout(a), "") == Wr.put_nat(_, "") : String}
      {==}

def WaitAny.wait_any_entry_answers(q, fit):
  +s = SpW.w_req(q, "")
  %Equal.sym(Wr.Dec<FWa.Req>, FWa.get_req(s), SpW.r_req(s), LW.wa.req(s)) : {FWa.ffi.got(_) == SpW.w_reply(q) : String}
  %Equal.sym(Wr.Dec<FWa.Req>, SpW.r_req(s), Wr.Got{q, ""}, LW.wa.req_rt(q, "", fit)) : {FWa.ffi.got(_) == SpW.w_reply(q) : String}
  wa.answer(q)
