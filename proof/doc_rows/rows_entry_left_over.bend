# eukhe: the proof of LAW rows_entry_left_over: the request reads back
# (as in rows_entry_answers) up to the rest, which is not empty

import Base
import ../../bend/doc_lines.bend as Dl
import ../../bend/doc_rows.bend as Dr
import ../../bend/ffi_doc_lines.bend as Fdl
import ../../bend/ffi_doc_rows.bend as Fdr
import ../../bend/wire.bend as Wr
import ../../laws/doc_rows.bend as DocRows
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/ffi_doc_lines/round_trip.bend as LFdlRoundTrip
import ./rows_entry_answers.bend as REA

def rlo.gate(+raw: Bool, +u8: Bool, +u16: Bool, +nul: Bool, +rest: String) -> {Fdr.ffi(DocRows.rows.spell_req_on(DocRows.rows.GateReq{raw, u8, u16, nul}, rest)) == Fdr.gate.done(raw, u8, u16, nul, Wr.end(rest)) : String}:
  +s4 = Wr.put_bool(nul, rest)
  +s3 = Wr.put_bool(u16, s4)
  +s2 = Wr.put_bool(u8, s3)
  +s1 = Wr.put_bool(raw, s2)
  +ans = Fdr.gate.done(raw, u8, u16, nul, Wr.end(rest))
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, s1)), Wr.Got{0n, s1}, Wire.wire_nat_round_trip(0n, s1, {==})) : {Fdr.run(_) == ans : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(s1), Wr.Got{raw, s2}, Wire.wire_bool_round_trip(raw, s2)) : {Fdr.gate.raw(_) == ans : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(s2), Wr.Got{u8, s3}, Wire.wire_bool_round_trip(u8, s3)) : {Fdr.gate.u8(raw, _) == ans : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(s3), Wr.Got{u16, s4}, Wire.wire_bool_round_trip(u16, s4)) : {Fdr.gate.u16(raw, u8, _) == ans : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(s4), Wr.Got{nul, rest}, Wire.wire_bool_round_trip(nul, rest)) : {Fdr.gate.nul(raw, u8, u16, _) == ans : String}
  {==}

def rlo.view(+sel: Dr.Sel, +u8: Bool, +over: Bool, +p: Dl.Proj, +rest: String, +h: {Bool.and(DocRows.rows.SelFits(sel), LawsBase.proj_fits(p)) == True{} : Bool}) -> {Fdr.ffi(DocRows.rows.spell_req_on(DocRows.rows.ViewReq{sel, u8, over, p}, rest)) == Fdr.view.done(sel, u8, over, p, Wr.end(rest)) : String}:
  +s3 = LawsBase.proj_spell(p, rest)
  +s2 = Wr.put_bool(over, s3)
  +s1 = Wr.put_bool(u8, s2)
  +s0 = DocRows.rows.spell_sel(sel, s1)
  +ans = Fdr.view.done(sel, u8, over, p, Wr.end(rest))
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, s0)), Wr.Got{1n, s0}, Wire.wire_nat_round_trip(1n, s0, {==})) : {Fdr.run(_) == ans : String}
  %Equal.sym(Wr.Dec<Dr.Sel>, Fdr.get_sel(s0), Wr.Got{sel, s1}, REA.rea_sel_rt(sel, s1, LLogicBool.wr_and_l(DocRows.rows.SelFits(sel), LawsBase.proj_fits(p), h))) : {Fdr.view.sel(_) == ans : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(s1), Wr.Got{u8, s2}, Wire.wire_bool_round_trip(u8, s2)) : {Fdr.view.u8(sel, _) == ans : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(s2), Wr.Got{over, s3}, Wire.wire_bool_round_trip(over, s3)) : {Fdr.view.over(sel, u8, _) == ans : String}
  %Equal.sym(Wr.Dec<Dl.Proj>, Fdl.get_proj(s3), Wr.Got{p, rest}, LFdlRoundTrip.fdlrt_proj(p, rest, LLogicBool.wr_and_r(DocRows.rows.SelFits(sel), LawsBase.proj_fits(p), h))) : {Fdr.view.proj(sel, u8, over, _) == ans : String}
  {==}

def DocRows.rows_entry_left_over(r, h, t, fit):
  match r:
    case DocRows.rows.GateReq{raw, u8, u16, nul}:
      rlo.gate(raw, u8, u16, nul, SCon{h, t})
    case DocRows.rows.ViewReq{sel, u8, over, p}:
      rlo.view(sel, u8, over, p, SCon{h, t}, fit)
