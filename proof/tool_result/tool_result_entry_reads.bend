# eukhe: the proof of LAW tool_result_entry_reads
#
# PROOF: the flag reads back (wire_bool_round_trip), then the blocks by
# the round trip of a list of Bools (LLog.pe.rt, after LA.trb.put_list
# turns the spec's spelling into the list encoder's; its count fits by the
# premise), so each stage of the decoder hands the next one exactly the
# rest after its field.

import Base
import ../../bend/tool_result.bend as Tr
import ../../bend/ffi_tool_result.bend as FTr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/tool_result.bend as ToolResult
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../log/base.bend as LLog
import ./base.bend as LA

def trr.req(q: FTr.Req, +rest: String, h: {ToolResult.sp_fit_req(q) == True{} : Bool}) -> {FTr.get_req(ToolResult.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FTr.Req>}:
  match q:
    case FTr.Req{+e, +ks}:
      +l = Wr.put_nat(List.length(&2, Bool, ks), ToolResult.sp_w_bools(ks, rest))
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(e, l)), Wr.Got{e, l}, Wire.wire_bool_round_trip(e, l)) : {FTr.get_req.err(_) == Wr.Got{FTr.Req{e, ks}, rest} : Wr.Dec<FTr.Req>}
      %LA.trb.put_list(ks, rest) : {FTr.get_req.imgs(e, Wr.get_list(~Bool, ~Wr.get_bool, _)) == Wr.Got{FTr.Req{e, ks}, rest} : Wr.Dec<FTr.Req>}
      %Equal.sym(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_list(~Bool, ~Wr.put_bool, ks, rest)), Wr.Got{ks, rest}, LLog.pe.rt(ks, rest, h)) : {FTr.get_req.imgs(e, _) == Wr.Got{FTr.Req{e, ks}, rest} : Wr.Dec<FTr.Req>}
      {==}

def ToolResult.tool_result_entry_reads(q, rest, h):
  trr.req(q, rest, h)
