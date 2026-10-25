# eukhe: the proof of LAW context_order_ffi_refuses

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

# PROOF of LAW context_order_ffi_refuses: the entry answers either the error form or an answer, and an answer opens with a Nat, never 'E' (cor.not_err).

def cof.done(q: FCo.Req, b: Bool, bad: {LawsBase.wire_opens_err(FCo.ffi.done(q, b)) == True{} : Bool}) -> {FCo.ffi.done(q, b) == Wr.err("context_order: malformed request") : String}:
  match b:
    case True{}:
      LACo.co.tf({FCo.answer(q) == Wr.err("context_order: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FCo.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FCo.answer(q)), True{}, bad), LACoReply.cor.not_err(q)))
    case False{}:
      {==}

def cof.got(d: Wr.Dec<FCo.Req>, bad: {LawsBase.wire_opens_err(FCo.ffi.got(d)) == True{} : Bool}) -> {FCo.ffi.got(d) == Wr.err("context_order: malformed request") : String}:
  match d:
    case Wr.Got{+q, +r}:
      cof.done(q, Wr.end(r), bad)
    case Wr.Bad{}:
      {==}

def ContextOrder.context_order_ffi_refuses(s, bad):
  cof.got(FCo.get_req(s), bad)
