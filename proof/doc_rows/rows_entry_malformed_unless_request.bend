# eukhe: the proof of LAW rows_entry_malformed_unless_request
#
# PROOF: follow the entry's decoders on s as rows_entry_exact does (its
# selector lemma fre_sel; Fdx for Nats and the projection; wire_bool_exact
# for flags): each field read is the spelling of its value, before the
# rest. A field that does not read, or an unknown tag, answers the
# malformed error, which the premise refutes; once the last field reads,
# s is the spelled request before what is left.

import Base
import ../../bend/doc_lines.bend as Dl
import ../../bend/doc_rows.bend as Dr
import ../../bend/ffi_doc_lines.bend as Fdl
import ../../bend/ffi_doc_rows.bend as Fdr
import ../../bend/wire.bend as Wr
import ../../laws/doc_rows.bend as DocRows
import ../../laws/base.bend as LawsBase
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../base/ffi_doc_lines/exact.bend as Fdx
import ./rows_entry_exact.bend as PRowsEntryExact

# the law's claim on s: s begins with a spelled request whose numbers fit
def rmu_G(s: String) -> Type:
  &r: DocRows.rows.Req -> &rest: String -> {(s, DocRows.rows.ReqFits(r)) == (DocRows.rows.spell_req_then(r, rest), True{}) : String & Bool}

def rmu_pair(-s: String, -x: String, -b: Bool, e1: {s == x : String}, e2: {b == True{} : Bool}) -> {(s, b) == (x, True{}) : String & Bool}:
  %Equal.sym(String, s, x, e1) : {(_, b) == (x, True{}) : String & Bool}
  %Equal.sym(Bool, b, True{}, e2) : {(x, _) == (x, True{}) : String & Bool}
  {==}

# ==== a gate request ====

# the fourth flag (nul): the request is read, the rest is what is left
def rmu_gate_nul(-s: String, +raw: Bool, +u8: Bool, +u16: Bool, -s5: String,
  e: {s == Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, s5)))) : String},
  d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s5, d),
  h: {String.eq(Fdr.gate.nul(raw, u8, u16, d), Wr.err("doc_rows: malformed request")) == False{} : Bool}) -> rmu_G(s):
  match d:
    case Wr.Got{+nul, +s6}:
      (DocRows.rows.GateReq{raw, u8, u16, nul}, (s6, rmu_pair(s, DocRows.rows.spell_req_then(DocRows.rows.GateReq{raw, u8, u16, nul}, s6), DocRows.rows.ReqFits(DocRows.rows.GateReq{raw, u8, u16, nul}),
        Equal.trans(String, s, Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, s5)))), Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, Wr.put_bool(nul, s6))))), e,
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, z)))), s5, Wr.put_bool(nul, s6), pb)), {==})))
    case Wr.Bad{}:
      Fdx.fdx_absurd(rmu_G(s), h)

# the third flag (utf16)
def rmu_gate_u16(-s: String, +raw: Bool, +u8: Bool, -s4: String,
  e: {s == Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, s4))) : String},
  d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s4, d),
  h: {String.eq(Fdr.gate.u16(raw, u8, d), Wr.err("doc_rows: malformed request")) == False{} : Bool}) -> rmu_G(s):
  match d:
    case Wr.Got{+u16, +s5}:
      rmu_gate_nul(s, raw, u8, u16, s5,
        Equal.trans(String, s, Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, s4))), Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, s5)))), e,
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, z))), s4, Wr.put_bool(u16, s5), pb)),
        Wr.get_bool(s5), PWireBoolExact.wr_bool_spec(s5), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(rmu_G(s), h)

# the second flag (utf8)
def rmu_gate_u8(-s: String, +raw: Bool, -s3: String, e: {s == Wr.put_nat(0n, Wr.put_bool(raw, s3)) : String},
  d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s3, d),
  h: {String.eq(Fdr.gate.u8(raw, d), Wr.err("doc_rows: malformed request")) == False{} : Bool}) -> rmu_G(s):
  match d:
    case Wr.Got{+u8, +s4}:
      rmu_gate_u16(s, raw, u8, s4,
        Equal.trans(String, s, Wr.put_nat(0n, Wr.put_bool(raw, s3)), Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, s4))), e,
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_bool(raw, z)), s3, Wr.put_bool(u8, s4), pb)),
        Wr.get_bool(s4), PWireBoolExact.wr_bool_spec(s4), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(rmu_G(s), h)

# tag 0, then the first flag (raw)
def rmu_gate_raw(-s: String, -s2: String, en: {s == Wr.put_nat(0n, s2) : String},
  d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s2, d),
  h: {String.eq(Fdr.gate.raw(d), Wr.err("doc_rows: malformed request")) == False{} : Bool}) -> rmu_G(s):
  match d:
    case Wr.Got{+raw, +s3}:
      rmu_gate_u8(s, raw, s3,
        Equal.trans(String, s, Wr.put_nat(0n, s2), Wr.put_nat(0n, Wr.put_bool(raw, s3)), en,
          Equal.cong(String, String, z => Wr.put_nat(0n, z), s2, Wr.put_bool(raw, s3), pb)),
        Wr.get_bool(s3), PWireBoolExact.wr_bool_spec(s3), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(rmu_G(s), h)

# ==== a view request ====

# the projection: the request is read, the rest is what is left
def rmu_view_proj(-s: String, +sel: Dr.Sel, +u8: Bool, +over: Bool, -s5: String,
  e: {s == Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, s5)))) : String},
  fs: {DocRows.rows.SelFits(sel) == True{} : Bool}, d: Wr.Dec<Dl.Proj>, pp: Fdx.fdx_pp(s5, d),
  h: {String.eq(Fdr.view.proj(sel, u8, over, d), Wr.err("doc_rows: malformed request")) == False{} : Bool}) -> rmu_G(s):
  match d:
    case Wr.Got{+p, +s6}:
      (ep, fp) = pp
      (DocRows.rows.ViewReq{sel, u8, over, p}, (s6, rmu_pair(s, DocRows.rows.spell_req_then(DocRows.rows.ViewReq{sel, u8, over, p}, s6), DocRows.rows.ReqFits(DocRows.rows.ViewReq{sel, u8, over, p}),
        Equal.trans(String, s, Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, s5)))), Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, LawsBase.proj_spell(p, s6))))), e,
          Equal.cong(String, String, z => Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, z)))), s5, LawsBase.proj_spell(p, s6), ep)),
        Fdx.fdx_and(DocRows.rows.SelFits(sel), LawsBase.proj_fits(p), fs, fp))))
    case Wr.Bad{}:
      Fdx.fdx_absurd(rmu_G(s), h)

# the over flag
def rmu_view_over(-s: String, +sel: Dr.Sel, +u8: Bool, -s4: String,
  e: {s == Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, s4))) : String},
  fs: {DocRows.rows.SelFits(sel) == True{} : Bool}, d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s4, d),
  h: {String.eq(Fdr.view.over(sel, u8, d), Wr.err("doc_rows: malformed request")) == False{} : Bool}) -> rmu_G(s):
  match d:
    case Wr.Got{+over, +s5}:
      rmu_view_proj(s, sel, u8, over, s5,
        Equal.trans(String, s, Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, s4))), Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, s5)))), e,
          Equal.cong(String, String, z => Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, z))), s4, Wr.put_bool(over, s5), pb)),
        fs, Fdl.get_proj(s5), Fdx.fdx_proj(s5), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(rmu_G(s), h)

# the utf8 flag
def rmu_view_u8(-s: String, +sel: Dr.Sel, -s3: String,
  e: {s == Wr.put_nat(1n, DocRows.rows.spell_sel(sel, s3)) : String},
  fs: {DocRows.rows.SelFits(sel) == True{} : Bool}, d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s3, d),
  h: {String.eq(Fdr.view.u8(sel, d), Wr.err("doc_rows: malformed request")) == False{} : Bool}) -> rmu_G(s):
  match d:
    case Wr.Got{+u8, +s4}:
      rmu_view_over(s, sel, u8, s4,
        Equal.trans(String, s, Wr.put_nat(1n, DocRows.rows.spell_sel(sel, s3)), Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, s4))), e,
          Equal.cong(String, String, z => Wr.put_nat(1n, DocRows.rows.spell_sel(sel, z)), s3, Wr.put_bool(u8, s4), pb)),
        fs, Wr.get_bool(s4), PWireBoolExact.wr_bool_spec(s4), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(rmu_G(s), h)

# tag 1, then a spelled selector that fits
def rmu_view_sel(-s: String, -s2: String, en: {s == Wr.put_nat(1n, s2) : String},
  d: Wr.Dec<Dr.Sel>, ps: PRowsEntryExact.fre_ps(s2, d),
  h: {String.eq(Fdr.view.sel(d), Wr.err("doc_rows: malformed request")) == False{} : Bool}) -> rmu_G(s):
  match d:
    case Wr.Got{+sel, +s3}:
      (es, fs) = ps
      rmu_view_u8(s, sel, s3,
        Equal.trans(String, s, Wr.put_nat(1n, s2), Wr.put_nat(1n, DocRows.rows.spell_sel(sel, s3)), en,
          Equal.cong(String, String, z => Wr.put_nat(1n, z), s2, DocRows.rows.spell_sel(sel, s3), es)),
        fs, Wr.get_bool(s3), PWireBoolExact.wr_bool_spec(s3), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(rmu_G(s), h)

# ==== the entry ====

# the request tag is 0 (gate) or 1 (view), else the malformed error
def rmu_entry(-s: String, d: Wr.Dec<Nat>, pn: Fdx.fdx_pn(s, d),
  h: {String.eq(Fdr.run(d), Wr.err("doc_rows: malformed request")) == False{} : Bool}) -> rmu_G(s):
  match d:
    case Wr.Got{t, +s2}:
      match t:
        case 0n:
          (en, fn) = pn
          rmu_gate_raw(s, s2, en, Wr.get_bool(s2), PWireBoolExact.wr_bool_spec(s2), h)
        case 1n:
          (en, fn) = pn
          rmu_view_sel(s, s2, en, Fdr.get_sel(s2), PRowsEntryExact.fre_sel(s2), h)
        case 2n+p:
          Fdx.fdx_absurd(rmu_G(s), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(rmu_G(s), h)

def DocRows.rows_entry_malformed_unless_request(s, other):
  rmu_entry(s, Wr.get_nat(s), Fdx.fdx_nat(s), other)
