# eukhe: the proof of LAW tool_result_entry_refuses
#
# PROOF: the entry answers either a plan, which opens with its count
# (never 'E': wire_nat_not_err), or the one error form; so an answer that
# opens with 'E' is that error form.

import Base
import ../../bend/tool_result.bend as Tr
import ../../bend/ffi_tool_result.bend as FTr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/tool_result.bend as ToolResult
import ../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../base/staging.bend as LStg
import ../base/wire_dec.bend as LE

def trf.answer_ok(q: FTr.Req) -> {LawsBase.wire_opens_err(FTr.answer(q)) == False{} : Bool}:
  match q:
    case FTr.Req{e, ks}:
      LE.dcw.fin_ok(Wr.put_list.go(~Tr.Out, ~FTr.put_out, Tr.plan(e, ks), ""))

def trf.refuse(d: Wr.Dec<FTr.Req>, bad: {LawsBase.wire_opens_err(FTr.ffi.got(d)) == True{} : Bool}) -> {FTr.ffi.got(d) == Wr.err("tool_result: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FTr.answer(q) == Wr.err("tool_result: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FTr.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FTr.answer(q)), True{}, bad), trf.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def ToolResult.tool_result_entry_refuses(s, bad):
  trf.refuse(FTr.get_req(s), bad)
