# eukhe: the proof of LAW gateway_commands_entry_reads
#
# PROOF: the text reads back by wire_str_round_trip and the session names
# by the list round trip of the shared wire lemmas (dcw.strs.rt; their
# lengths fit by the premise), so each stage of the decoder hands the next
# one exactly the rest after its field.

import Base
import ../../bend/ffi_gateway_commands.bend as FGc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_commands.bend as GatewayCommands
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire_strs.bend as LS

def gcr.req(q: FGc.Req, +rest: String, h: {GatewayCommands.gc_fit_req(q) == True{} : Bool}) -> {FGc.get_req(GatewayCommands.gc_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FGc.Req>}:
  match q:
    case FGc.QParse{+t, +ns}:
      +hq = h
      +fs = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(String.length(t)), Bool.and(LawsBase.wire_fits(List.length(&2, String, ns)), DocCommit.sp_fit_strs(ns)), hq)
      +fn = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(List.length(&2, String, ns)), DocCommit.sp_fit_strs(ns), fs)
      +fd = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(List.length(&2, String, ns)), DocCommit.sp_fit_strs(ns), fs)
      +l = Wr.put_list(~String, ~Wr.put_str, ns, rest)
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(t, l)), Wr.Got{t, l}, Wire.wire_str_round_trip(t, l, LLogicBool.tree.pt.and_l(LawsBase.wire_fits(String.length(t)), Bool.and(LawsBase.wire_fits(List.length(&2, String, ns)), DocCommit.sp_fit_strs(ns)), hq))) : {FGc.get_req.text(_) == Wr.Got{FGc.QParse{t, ns}, rest} : Wr.Dec<FGc.Req>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, l), Wr.Got{ns, rest}, LS.dcw.strs.rt(ns, rest, fn, fd)) : {FGc.get_req.sessions(t, _) == Wr.Got{FGc.QParse{t, ns}, rest} : Wr.Dec<FGc.Req>}
      {==}

def GatewayCommands.gateway_commands_entry_reads(q, rest, h):
  gcr.req(q, rest, h)
