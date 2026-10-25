# eukhe: the proof of LAW compaction_cut_ffi_exact

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
import ./base/exact.bend as LACcExact

# PROOF of LAW compaction_cut_ffi_exact: the request decoder answers Got only for a spelled request whose numbers fit (cce.req); the entry answers a value only when nothing is left after it.

def ccx.top(-s: String, d: Wr.Dec<FCc.Req>, p: LACcExact.cce.RQ(s, d), ok: {LawsBase.wire_opens_err(FCc.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FCc.Req, q2 => {s == CompactionCut.spell_req(q2, "") : String} & {CompactionCut.req_fits(q2) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, p)
        case SCon{x, y}:
          LACo.co.tf(Sigma<&1, &1, FCc.Req, q2 => {s == CompactionCut.spell_req(q2, "") : String} & {CompactionCut.req_fits(q2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LACo.co.tf(Sigma<&1, &1, FCc.Req, q2 => {s == CompactionCut.spell_req(q2, "") : String} & {CompactionCut.req_fits(q2) == True{} : Bool}>, ok)

def CompactionCut.compaction_cut_ffi_exact(s, ok):
  ccx.top(s, FCc.get_req(s), LACcExact.cce.req(s), ok)
