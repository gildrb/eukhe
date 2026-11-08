# eukhe: the proof of LAW rows_entry_left_over_exact: follow the entry's
# decoders on s, each stage spelled and fitting (as in rows_entry_exact);
# the left-over error comes only from the last stage with input after the
# request; a failed stage answers the malformed form, and a whole request
# an answer that never opens with 'E' (rows_entry_errors' lemmas)

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
import ./rows_entry_exact.bend as RE
import ./rows_entry_errors.bend as RER

# the law's claim on s
def rlx.Ex(s: String) -> Type:
  Sigma<&1, &1, DocRows.rows.LeftOver, w => {s == DocRows.rows.spell_left_over(w) : String} & {DocRows.rows.ReqFits(DocRows.rows.left_req(w)) == True{} : Bool}>

# the malformed text is not the left-over text
def rlx.bad(-s: String, e: {Wr.err("doc_rows: malformed request") == Wr.err("doc_rows: input left over") : String}) -> rlx.Ex(s):
  Fdx.fdx_absurd(rlx.Ex(s), Equal.sym(Bool, False{}, True{}, Equal.cong(String, Bool, z => LawsBase.text_same(z, Wr.err("doc_rows: input left over")), Wr.err("doc_rows: malformed request"), Wr.err("doc_rows: input left over"), e)))

# an answer is not the left-over text
def rlx.ans(-s: String, -x: String, ok: {LawsBase.wire_opens_err(x) == False{} : Bool}, e: {x == Wr.err("doc_rows: input left over") : String}) -> rlx.Ex(s):
  RER.rer.no(rlx.Ex(s), x, ok, Equal.cong(String, Bool, z => LawsBase.wire_opens_err(z), x, Wr.err("doc_rows: input left over"), e))

# ==== a gate request ====

def rlx.gate_done(+s6: String, -s: String, +raw: Bool, +u8: Bool, +u16: Bool, +nul: Bool,
  e: {s == Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, Wr.put_bool(nul, s6))))) : String},
  h: {Fdr.gate.done(raw, u8, u16, nul, Wr.end(s6)) == Wr.err("doc_rows: input left over") : String}) -> rlx.Ex(s):
  match s6:
    case SNil{}:
      rlx.ans(s, Fdr.put_gate(Dr.gate(raw, u8, u16, nul)), RER.rer.gate_ok(Dr.gate(raw, u8, u16, nul)), h)
    case SCon{+ch, +t}:
      (DocRows.rows.LeftOver{DocRows.rows.GateReq{raw, u8, u16, nul}, ch, t}, (e, {==}))

def rlx.gate_nul(-s: String, +raw: Bool, +u8: Bool, +u16: Bool, -s5: String,
  e: {s == Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, s5)))) : String},
  d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s5, d),
  h: {Fdr.gate.nul(raw, u8, u16, d) == Wr.err("doc_rows: input left over") : String}) -> rlx.Ex(s):
  match d:
    case Wr.Got{+nul, +s6}:
      rlx.gate_done(s6, s, raw, u8, u16, nul,
        Equal.trans(String, s, Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, s5)))), Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, Wr.put_bool(nul, s6))))), e,
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, z)))), s5, Wr.put_bool(nul, s6), pb)), h)
    case Wr.Bad{}:
      rlx.bad(s, h)

def rlx.gate_u16(-s: String, +raw: Bool, +u8: Bool, -s4: String,
  e: {s == Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, s4))) : String},
  d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s4, d),
  h: {Fdr.gate.u16(raw, u8, d) == Wr.err("doc_rows: input left over") : String}) -> rlx.Ex(s):
  match d:
    case Wr.Got{+u16, +s5}:
      rlx.gate_nul(s, raw, u8, u16, s5,
        Equal.trans(String, s, Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, s4))), Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, s5)))), e,
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, z))), s4, Wr.put_bool(u16, s5), pb)),
        Wr.get_bool(s5), PWireBoolExact.wr_bool_spec(s5), h)
    case Wr.Bad{}:
      rlx.bad(s, h)

def rlx.gate_u8(-s: String, +raw: Bool, -s3: String, e: {s == Wr.put_nat(0n, Wr.put_bool(raw, s3)) : String},
  d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s3, d),
  h: {Fdr.gate.u8(raw, d) == Wr.err("doc_rows: input left over") : String}) -> rlx.Ex(s):
  match d:
    case Wr.Got{+u8, +s4}:
      rlx.gate_u16(s, raw, u8, s4,
        Equal.trans(String, s, Wr.put_nat(0n, Wr.put_bool(raw, s3)), Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, s4))), e,
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_bool(raw, z)), s3, Wr.put_bool(u8, s4), pb)),
        Wr.get_bool(s4), PWireBoolExact.wr_bool_spec(s4), h)
    case Wr.Bad{}:
      rlx.bad(s, h)

def rlx.gate_raw(-s: String, -s2: String, en: {s == Wr.put_nat(0n, s2) : String},
  d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s2, d),
  h: {Fdr.gate.raw(d) == Wr.err("doc_rows: input left over") : String}) -> rlx.Ex(s):
  match d:
    case Wr.Got{+raw, +s3}:
      rlx.gate_u8(s, raw, s3,
        Equal.trans(String, s, Wr.put_nat(0n, s2), Wr.put_nat(0n, Wr.put_bool(raw, s3)), en,
          Equal.cong(String, String, z => Wr.put_nat(0n, z), s2, Wr.put_bool(raw, s3), pb)),
        Wr.get_bool(s3), PWireBoolExact.wr_bool_spec(s3), h)
    case Wr.Bad{}:
      rlx.bad(s, h)

# ==== a view request ====

def rlx.view_done(+s6: String, -s: String, +sel: Dr.Sel, +u8: Bool, +over: Bool, +p: Dl.Proj,
  e: {s == Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, LawsBase.proj_spell(p, s6))))) : String},
  fs: {DocRows.rows.SelFits(sel) == True{} : Bool}, fp: {LawsBase.proj_fits(p) == True{} : Bool},
  h: {Fdr.view.done(sel, u8, over, p, Wr.end(s6)) == Wr.err("doc_rows: input left over") : String}) -> rlx.Ex(s):
  match s6:
    case SNil{}:
      rlx.ans(s, Fdr.put_view(Dr.view(sel, u8, over, p)), RER.rer.view_ok(Dr.view(sel, u8, over, p)), h)
    case SCon{+ch, +t}:
      (DocRows.rows.LeftOver{DocRows.rows.ViewReq{sel, u8, over, p}, ch, t}, (e, Fdx.fdx_and(DocRows.rows.SelFits(sel), LawsBase.proj_fits(p), fs, fp)))

def rlx.view_proj(-s: String, +sel: Dr.Sel, +u8: Bool, +over: Bool, -s5: String,
  e: {s == Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, s5)))) : String},
  fs: {DocRows.rows.SelFits(sel) == True{} : Bool}, d: Wr.Dec<Dl.Proj>, pp: Fdx.fdx_pp(s5, d),
  h: {Fdr.view.proj(sel, u8, over, d) == Wr.err("doc_rows: input left over") : String}) -> rlx.Ex(s):
  match d:
    case Wr.Got{+p, +s6}:
      (ep, fp) = pp
      rlx.view_done(s6, s, sel, u8, over, p,
        Equal.trans(String, s, Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, s5)))), Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, LawsBase.proj_spell(p, s6))))), e,
          Equal.cong(String, String, z => Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, z)))), s5, LawsBase.proj_spell(p, s6), ep)),
        fs, fp, h)
    case Wr.Bad{}:
      rlx.bad(s, h)

def rlx.view_over(-s: String, +sel: Dr.Sel, +u8: Bool, -s4: String,
  e: {s == Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, s4))) : String},
  fs: {DocRows.rows.SelFits(sel) == True{} : Bool}, d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s4, d),
  h: {Fdr.view.over(sel, u8, d) == Wr.err("doc_rows: input left over") : String}) -> rlx.Ex(s):
  match d:
    case Wr.Got{+over, +s5}:
      rlx.view_proj(s, sel, u8, over, s5,
        Equal.trans(String, s, Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, s4))), Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, s5)))), e,
          Equal.cong(String, String, z => Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, z))), s4, Wr.put_bool(over, s5), pb)),
        fs, Fdl.get_proj(s5), Fdx.fdx_proj(s5), h)
    case Wr.Bad{}:
      rlx.bad(s, h)

def rlx.view_u8(-s: String, +sel: Dr.Sel, -s3: String,
  e: {s == Wr.put_nat(1n, DocRows.rows.spell_sel(sel, s3)) : String},
  fs: {DocRows.rows.SelFits(sel) == True{} : Bool}, d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s3, d),
  h: {Fdr.view.u8(sel, d) == Wr.err("doc_rows: input left over") : String}) -> rlx.Ex(s):
  match d:
    case Wr.Got{+u8, +s4}:
      rlx.view_over(s, sel, u8, s4,
        Equal.trans(String, s, Wr.put_nat(1n, DocRows.rows.spell_sel(sel, s3)), Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, s4))), e,
          Equal.cong(String, String, z => Wr.put_nat(1n, DocRows.rows.spell_sel(sel, z)), s3, Wr.put_bool(u8, s4), pb)),
        fs, Wr.get_bool(s4), PWireBoolExact.wr_bool_spec(s4), h)
    case Wr.Bad{}:
      rlx.bad(s, h)

def rlx.view_sel(-s: String, -s2: String, en: {s == Wr.put_nat(1n, s2) : String},
  d: Wr.Dec<Dr.Sel>, ps: RE.fre_ps(s2, d),
  h: {Fdr.view.sel(d) == Wr.err("doc_rows: input left over") : String}) -> rlx.Ex(s):
  match d:
    case Wr.Got{+sel, +s3}:
      (es, fs) = ps
      rlx.view_u8(s, sel, s3,
        Equal.trans(String, s, Wr.put_nat(1n, s2), Wr.put_nat(1n, DocRows.rows.spell_sel(sel, s3)), en,
          Equal.cong(String, String, z => Wr.put_nat(1n, z), s2, DocRows.rows.spell_sel(sel, s3), es)),
        fs, Wr.get_bool(s3), PWireBoolExact.wr_bool_spec(s3), h)
    case Wr.Bad{}:
      rlx.bad(s, h)

# ==== the entry ====

def rlx.entry(-s: String, d: Wr.Dec<Nat>, pn: Fdx.fdx_pn(s, d),
  h: {Fdr.run(d) == Wr.err("doc_rows: input left over") : String}) -> rlx.Ex(s):
  match d:
    case Wr.Got{t, +s2}:
      match t:
        case 0n:
          (en, fn) = pn
          rlx.gate_raw(s, s2, en, Wr.get_bool(s2), PWireBoolExact.wr_bool_spec(s2), h)
        case 1n:
          (en, fn) = pn
          rlx.view_sel(s, s2, en, Fdr.get_sel(s2), RE.fre_sel(s2), h)
        case 2n+p:
          rlx.bad(s, h)
    case Wr.Bad{}:
      rlx.bad(s, h)

def DocRows.rows_entry_left_over_exact(s, e):
  rlx.entry(s, Wr.get_nat(s), Fdx.fdx_nat(s), e)
