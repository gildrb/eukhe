# eukhe: the proof of LAW context_order_ffi_exact

import Base
import ../../bend/context_order.bend as Co
import ../../bend/ffi_context_order.bend as FCo
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/context_order.bend as ContextOrder
import ./base.bend as LACo
import ./base/reply.bend as LACoReply
import ./base/exact.bend as LACoExact

# PROOF of LAW context_order_ffi_exact: the request decoder answers Got only for a spelled request whose numbers fit (coe.req: the wire's exactness laws, stage by stage); the entry answers a value only when nothing is left after it.

def cox.top(-s: String, d: Wr.Dec<FCo.Req>, p: LACoExact.coe.RQ(s, d), ok: {LawsBase.wire_opens_err(FCo.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FCo.Req, q2 => {s == ContextOrder.spell_req(q2, "") : String} & {ContextOrder.req_fits(q2) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, p)
        case SCon{x, y}:
          LACo.co.tf(Sigma<&1, &1, FCo.Req, q2 => {s == ContextOrder.spell_req(q2, "") : String} & {ContextOrder.req_fits(q2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LACo.co.tf(Sigma<&1, &1, FCo.Req, q2 => {s == ContextOrder.spell_req(q2, "") : String} & {ContextOrder.req_fits(q2) == True{} : Bool}>, ok)

def ContextOrder.context_order_ffi_exact(s, ok):
  cox.top(s, FCo.get_req(s), LACoExact.coe.req(s), ok)
