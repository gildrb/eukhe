# eukhe: the proof of LAW compaction_cut_ffi_refuses

import Base
import ../../bend/context_order.bend as Co
import ../../bend/compaction_cut.bend as Cc
import ../../bend/ffi_compaction_cut.bend as FCc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/context_order.bend as ContextOrder
import ../../laws/compaction_cut.bend as CompactionCut
import ../context_order/base.bend as LACo
import ./base/reply.bend as LACcReply

# PROOF of LAW compaction_cut_ffi_refuses: the entry answers either the error form or an answer, and an answer opens with a Nat, never 'E' (ccr.not_err).

def ccf.done(q: FCc.Req, b: Bool, bad: {LawsBase.wire_opens_err(FCc.ffi.done(q, b)) == True{} : Bool}) -> {FCc.ffi.done(q, b) == Wr.err("compaction_cut: malformed request") : String}:
  match b:
    case True{}:
      LACo.co.tf({FCc.answer(q) == Wr.err("compaction_cut: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FCc.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FCc.answer(q)), True{}, bad), LACcReply.ccr.not_err(q)))
    case False{}:
      {==}

def ccf.got(d: Wr.Dec<FCc.Req>, bad: {LawsBase.wire_opens_err(FCc.ffi.got(d)) == True{} : Bool}) -> {FCc.ffi.got(d) == Wr.err("compaction_cut: malformed request") : String}:
  match d:
    case Wr.Got{+q, +r}:
      ccf.done(q, Wr.end(r), bad)
    case Wr.Bad{}:
      {==}

def CompactionCut.compaction_cut_ffi_refuses(s, bad):
  ccf.got(FCc.get_req(s), bad)
