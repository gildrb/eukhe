# eukhe: the proof of LAW rows_entry_errors: every stage of the entry's
# decoders answers the malformed error form when it fails; the last one
# answers the left-over error form for input after the request, else an
# answer, which opens with a Nat (wire_nat_not_err), never 'E'

import Base
import ../../bend/doc_lines.bend as Dl
import ../../bend/doc_rows.bend as Dr
import ../../bend/ffi_doc_lines.bend as Fdl
import ../../bend/ffi_doc_rows.bend as Fdr
import ../../bend/wire.bend as Wr
import ../../laws/doc_rows.bend as DocRows
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/ffi_doc_lines/exact.bend as Fdx

# the law's claim on a reply x
def rer.G(x: String) -> Type:
  {Bool.or(LawsBase.text_same(x, Wr.err("doc_rows: malformed request")), LawsBase.text_same(x, Wr.err("doc_rows: input left over"))) == True{} : Bool}

# an answer never opens with 'E': refute e
def rer.no(-G: Type, -x: String, ok: {LawsBase.wire_opens_err(x) == False{} : Bool}, e: {LawsBase.wire_opens_err(x) == True{} : Bool}) -> G:
  Fdx.fdx_absurd(G, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(x), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(x), True{}, e), ok))

def rer.gate_ok(g: Dr.Gate) -> {LawsBase.wire_opens_err(Fdr.put_gate(g)) == False{} : Bool}:
  match g:
    case Dr.Go{}:
      {==}
    case Dr.NotUtf8{}:
      {==}
    case Dr.Binary{}:
      {==}

def rer.view_ok(v: Dr.View) -> {LawsBase.wire_opens_err(Fdr.put_view(v)) == False{} : Bool}:
  match v:
    case Dr.View{t, raw, sp, ns, tag}:
      Wire.wire_nat_not_err(t, Wr.put_bool(raw, Wr.put_list(~Dr.Span, ~Fdr.put_span, sp, Wr.put_list(~Dr.Note, ~Fdr.put_note, ns, Wr.put_bool(tag, "")))))

def rer.gate_done(s6: String, +raw: Bool, +u8: Bool, +u16: Bool, +nul: Bool, e: {LawsBase.wire_opens_err(Fdr.gate.done(raw, u8, u16, nul, Wr.end(s6))) == True{} : Bool}) -> rer.G(Fdr.gate.done(raw, u8, u16, nul, Wr.end(s6))):
  match s6:
    case SNil{}:
      rer.no(rer.G(Fdr.gate.done(raw, u8, u16, nul, True{})), Fdr.put_gate(Dr.gate(raw, u8, u16, nul)), rer.gate_ok(Dr.gate(raw, u8, u16, nul)), e)
    case SCon{c, t}:
      {==}

def rer.gate_nul(+raw: Bool, +u8: Bool, +u16: Bool, d: Wr.Dec<Bool>, e: {LawsBase.wire_opens_err(Fdr.gate.nul(raw, u8, u16, d)) == True{} : Bool}) -> rer.G(Fdr.gate.nul(raw, u8, u16, d)):
  match d:
    case Wr.Got{nul, s6}:
      rer.gate_done(s6, raw, u8, u16, nul, e)
    case Wr.Bad{}:
      {==}

def rer.gate_u16(+raw: Bool, +u8: Bool, d: Wr.Dec<Bool>, e: {LawsBase.wire_opens_err(Fdr.gate.u16(raw, u8, d)) == True{} : Bool}) -> rer.G(Fdr.gate.u16(raw, u8, d)):
  match d:
    case Wr.Got{u16, s5}:
      rer.gate_nul(raw, u8, u16, Wr.get_bool(s5), e)
    case Wr.Bad{}:
      {==}

def rer.gate_u8(+raw: Bool, d: Wr.Dec<Bool>, e: {LawsBase.wire_opens_err(Fdr.gate.u8(raw, d)) == True{} : Bool}) -> rer.G(Fdr.gate.u8(raw, d)):
  match d:
    case Wr.Got{u8, s4}:
      rer.gate_u16(raw, u8, Wr.get_bool(s4), e)
    case Wr.Bad{}:
      {==}

def rer.gate_raw(d: Wr.Dec<Bool>, e: {LawsBase.wire_opens_err(Fdr.gate.raw(d)) == True{} : Bool}) -> rer.G(Fdr.gate.raw(d)):
  match d:
    case Wr.Got{raw, s3}:
      rer.gate_u8(raw, Wr.get_bool(s3), e)
    case Wr.Bad{}:
      {==}

def rer.view_done(s6: String, +sel: Dr.Sel, +u8: Bool, +over: Bool, +p: Dl.Proj, e: {LawsBase.wire_opens_err(Fdr.view.done(sel, u8, over, p, Wr.end(s6))) == True{} : Bool}) -> rer.G(Fdr.view.done(sel, u8, over, p, Wr.end(s6))):
  match s6:
    case SNil{}:
      rer.no(rer.G(Fdr.view.done(sel, u8, over, p, True{})), Fdr.put_view(Dr.view(sel, u8, over, p)), rer.view_ok(Dr.view(sel, u8, over, p)), e)
    case SCon{c, t}:
      {==}

def rer.view_proj(+sel: Dr.Sel, +u8: Bool, +over: Bool, d: Wr.Dec<Dl.Proj>, e: {LawsBase.wire_opens_err(Fdr.view.proj(sel, u8, over, d)) == True{} : Bool}) -> rer.G(Fdr.view.proj(sel, u8, over, d)):
  match d:
    case Wr.Got{p, s6}:
      rer.view_done(s6, sel, u8, over, p, e)
    case Wr.Bad{}:
      {==}

def rer.view_over(+sel: Dr.Sel, +u8: Bool, d: Wr.Dec<Bool>, e: {LawsBase.wire_opens_err(Fdr.view.over(sel, u8, d)) == True{} : Bool}) -> rer.G(Fdr.view.over(sel, u8, d)):
  match d:
    case Wr.Got{over, s5}:
      rer.view_proj(sel, u8, over, Fdl.get_proj(s5), e)
    case Wr.Bad{}:
      {==}

def rer.view_u8(+sel: Dr.Sel, d: Wr.Dec<Bool>, e: {LawsBase.wire_opens_err(Fdr.view.u8(sel, d)) == True{} : Bool}) -> rer.G(Fdr.view.u8(sel, d)):
  match d:
    case Wr.Got{u8, s4}:
      rer.view_over(sel, u8, Wr.get_bool(s4), e)
    case Wr.Bad{}:
      {==}

def rer.view_sel(d: Wr.Dec<Dr.Sel>, e: {LawsBase.wire_opens_err(Fdr.view.sel(d)) == True{} : Bool}) -> rer.G(Fdr.view.sel(d)):
  match d:
    case Wr.Got{sel, s3}:
      rer.view_u8(sel, Wr.get_bool(s3), e)
    case Wr.Bad{}:
      {==}

def rer.run(d: Wr.Dec<Nat>, e: {LawsBase.wire_opens_err(Fdr.run(d)) == True{} : Bool}) -> rer.G(Fdr.run(d)):
  match d:
    case Wr.Got{t, s2}:
      match t:
        case 0n:
          rer.gate_raw(Wr.get_bool(s2), e)
        case 1n:
          rer.view_sel(Fdr.get_sel(s2), e)
        case 2n+p:
          {==}
    case Wr.Bad{}:
      {==}

def DocRows.rows_entry_errors(s, e):
  rer.run(Wr.get_nat(s), e)
