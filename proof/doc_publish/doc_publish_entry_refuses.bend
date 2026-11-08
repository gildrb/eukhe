# eukhe: the proof of LAW doc_publish_entry_refuses
#
# PROOF: the entry answers either a step, which opens with a digit (never
# 'E'), or the one error form; so an answer that opens with 'E' is that
# error form.

import Base
import ../../bend/doc_publish.bend as Dp
import ../../bend/ffi_doc_publish.bend as FDp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/doc_publish.bend as DocPublish
import ../base/staging.bend as LStg

def dpf.step_ok(p: Dp.Step) -> {LawsBase.wire_opens_err(FDp.put_step(p)) == False{} : Bool}:
  match p:
    case Dp.Place{}:
      {==}
    case Dp.Rebase{}:
      {==}
    case Dp.Refuse{}:
      {==}

def dpf.answer_ok(q: FDp.Req) -> {LawsBase.wire_opens_err(FDp.answer(q)) == False{} : Bool}:
  match q:
    case FDp.Req{k, s}:
      dpf.step_ok(Dp.step(k, s))

def dpf.refuse(d: Wr.Dec<FDp.Req>, bad: {LawsBase.wire_opens_err(FDp.ffi.got(d)) == True{} : Bool}) -> {FDp.ffi.got(d) == Wr.err("doc_publish: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FDp.answer(q) == Wr.err("doc_publish: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FDp.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FDp.answer(q)), True{}, bad), dpf.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def DocPublish.doc_publish_entry_refuses(s, bad):
  dpf.refuse(FDp.get_req(s), bad)
