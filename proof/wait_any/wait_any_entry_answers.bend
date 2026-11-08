# eukhe: the proof of LAW wait_any_entry_answers
#
# PROOF: the spelled request reads back whole through the entry's
# decoder with nothing left (wa.req_rt), so the entry answers the model's
# decision, spelled as the grammar spells it (wae.put_pick, wae.put_out).

import Base
import ../../bend/wait_any.bend as Wa
import ../../spec/durable/wait_any.bend as WaSpec
import ../../laws/wait_any.bend as WaitAny
import ../../bend/ffi_wait_any.bend as FWa
import ../../bend/wire.bend as Wr
import ../../spec/durable/wait_any_wire.bend as SpW
import ./base.bend as LW

def wae.put_pick(p: Wa.Pick) -> {FWa.put_pick(p) == SpW.w_pick(p) : String}:
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

def wae.put_out(o: Wa.Out) -> {FWa.put_step(o) == SpW.w_out(o) : String}:
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

# the entry's answer to a request is the model's decision, spelled
def wae.answer(q: FWa.Req) -> {FWa.answer(q) == SpW.w_reply(q) : String}:
  match q:
    case FWa.QPoll{+n, +c, +l, +ts}:
      wae.put_pick(Wa.poll(n, c, l, ts))
    case FWa.QStep{+k, +d, +e}:
      wae.put_out(Wa.step(k, d, e))
    case FWa.QTimeout{+a}:
      {==}

def WaitAny.wait_any_entry_answers(q, fit):
  %Equal.sym(Wr.Dec<FWa.Req>, FWa.get_req(SpW.w_req(q, "")), Wr.Got{q, ""}, LW.wa.req_rt(q, "", fit)) : {FWa.ffi.got(_) == SpW.w_reply(q) : String}
  wae.answer(q)
