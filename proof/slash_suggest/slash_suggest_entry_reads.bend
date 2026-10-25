# eukhe: the proof of LAW slash_suggest_entry_reads
#
# PROOF: the typed name reads back by wire_str_round_trip and the candidates
# by the list round trip of the shared wire lemmas (dcw.strs.rt; their
# lengths fit by the premise), so each stage of the decoder hands the next
# one exactly the rest after its field.

import Base
import ../../bend/slash_suggest.bend as Ss
import ../../bend/ffi_slash_suggest.bend as FSs
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/slash_suggest.bend as SlashSuggest
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire_strs.bend as LS
import ./base.bend as LA

def ssr.req(q: FSs.Req, +rest: String, h: {SlashSuggest.sp_fit_req(q) == True{} : Bool}) -> {FSs.get_req(SlashSuggest.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FSs.Req>}:
  match q:
    case FSs.QSuggest{+w, +cs}:
      +hq = h
      +fs = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(String.length(w)), Bool.and(LawsBase.wire_fits(List.length(&2, String, cs)), SlashSuggest.sp_fit_strs(cs)), hq)
      +fn = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(List.length(&2, String, cs)), SlashSuggest.sp_fit_strs(cs), fs)
      +fd = Equal.trans(Bool, DocCommit.sp_fit_strs(cs), SlashSuggest.sp_fit_strs(cs), True{}, Equal.sym(Bool, SlashSuggest.sp_fit_strs(cs), DocCommit.sp_fit_strs(cs), LA.ssb.fits(cs)), LLogicBool.tree.pt.and_r(LawsBase.wire_fits(List.length(&2, String, cs)), SlashSuggest.sp_fit_strs(cs), fs))
      +l = Wr.put_list(~String, ~Wr.put_str, cs, rest)
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(w, l)), Wr.Got{w, l}, Wire.wire_str_round_trip(w, l, LLogicBool.tree.pt.and_l(LawsBase.wire_fits(String.length(w)), Bool.and(LawsBase.wire_fits(List.length(&2, String, cs)), SlashSuggest.sp_fit_strs(cs)), hq))) : {FSs.get_req.typed(_) == Wr.Got{FSs.QSuggest{w, cs}, rest} : Wr.Dec<FSs.Req>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, l), Wr.Got{cs, rest}, LS.dcw.strs.rt(cs, rest, fn, fd)) : {FSs.get_req.names(w, _) == Wr.Got{FSs.QSuggest{w, cs}, rest} : Wr.Dec<FSs.Req>}
      {==}

def SlashSuggest.slash_suggest_entry_reads(q, rest, h):
  ssr.req(q, rest, h)
