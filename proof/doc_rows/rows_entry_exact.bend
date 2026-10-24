# eukhe: the proof of LAW rows_entry_exact

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

# the law's claim on s: s spells a request whose numbers fit
def fre_Ex(s: String) -> Type:
  &r: DocRows.rows.Req -> ({s == DocRows.rows.spell_req(r) : String} & {DocRows.rows.ReqFits(r) == True{} : Bool})

# ==== Maybe<Nat> ====

# what a Maybe<Nat> decoder's answer says about its input s
def fre_pmn(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+m, r}:
      {s == DocRows.rows.spell_mnat(m, r) : String} & {LawsBase.wire_mfits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# tag 1, then a spelled Nat that fits
def fre_mnat_some(-s: String, -s2: String, en: {s == Wr.put_nat(1n, s2) : String}, d: Wr.Dec<Nat>,
  pn: Fdx.fdx_pn(s2, d)) -> fre_pmn(s, Fdr.get_mnat.some(d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, f) = pn
      (Equal.trans(String, s, Wr.put_nat(1n, s2), Wr.put_nat(1n, Wr.put_nat(n, r)), en,
        Equal.cong(String, String, z => Wr.put_nat(1n, z), s2, Wr.put_nat(n, r), e)), f)
    case Wr.Bad{}:
      Unit{}

# the Maybe tag is 0 or 1 (then a Nat)
def fre_mnat_tag(-s: String, d: Wr.Dec<Nat>, pn: Fdx.fdx_pn(s, d)) -> fre_pmn(s, Fdr.get_mnat.tag(d)):
  match d:
    case Wr.Got{t, +r}:
      match t:
        case 0n:
          (e, f) = pn
          (e, {==})
        case 1n:
          (e, f) = pn
          fre_mnat_some(s, r, e, Wr.get_nat(r), Fdx.fdx_nat(r))
        case 2n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# every Maybe<Nat> the decoder reads is spelled and fits
def fre_mnat(+s: String) -> fre_pmn(s, Fdr.get_mnat(s)):
  fre_mnat_tag(s, Wr.get_nat(s), Fdx.fdx_nat(s))

# ==== a range ====

# what a range decoder's answer says about its input s
def fre_pr(s: String, d: Wr.Dec<Dr.Range>) -> Type:
  match d:
    case Wr.Got{x, r}:
      match x:
        case Dr.Range{+st, +m}:
          {s == Wr.put_nat(st, DocRows.rows.spell_mnat(m, r)) : String} & {Bool.and(LawsBase.wire_fits(st), LawsBase.wire_mfits(m)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a spelled start, then a spelled end
def fre_range_end(-s: String, -st: Nat, -s2: String, en: {s == Wr.put_nat(st, s2) : String},
  fn: {LawsBase.wire_fits(st) == True{} : Bool}, d: Wr.Dec<Maybe<&2, Nat>>, pm: fre_pmn(s2, d))
  -> fre_pr(s, Fdr.get_range.end(st, d)):
  match d:
    case Wr.Got{+m, +r}:
      (em, fm) = pm
      (Equal.trans(String, s, Wr.put_nat(st, s2), Wr.put_nat(st, DocRows.rows.spell_mnat(m, r)), en,
        Equal.cong(String, String, z => Wr.put_nat(st, z), s2, DocRows.rows.spell_mnat(m, r), em)),
        Fdx.fdx_and(LawsBase.wire_fits(st), LawsBase.wire_mfits(m), fn, fm))
    case Wr.Bad{}:
      Unit{}

# a spelled start that fits, then the end
def fre_range_start(-s: String, d: Wr.Dec<Nat>, pn: Fdx.fdx_pn(s, d)) -> fre_pr(s, Fdr.get_range.start(d)):
  match d:
    case Wr.Got{+st, +r}:
      (en, fn) = pn
      fre_range_end(s, st, r, en, fn, Fdr.get_mnat(r), fre_mnat(r))
    case Wr.Bad{}:
      Unit{}

# every range the decoder reads is spelled and fits
def fre_range(+s: String) -> fre_pr(s, Fdr.get_range(s)):
  fre_range_start(s, Wr.get_nat(s), Fdx.fdx_nat(s))

# ==== a list of ranges ====

# the spellings of the ranges xs, then rest
def fre_ranges_items(xs: List<&2, Dr.Range>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      DocRows.rows.spell_range(x, fre_ranges_items(t, rest))

# the list encoder's loop: the count and the items
def fre_ranges_go(xs: List<&2, Dr.Range>, -rest: String) -> {Wr.put_list.go(~Dr.Range, ~DocRows.rows.spell_range, xs, rest) == (List.length(&2, Dr.Range, xs), fre_ranges_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Dr.Range, ~DocRows.rows.spell_range, t, rest), (List.length(&2, Dr.Range, t), fre_ranges_items(t, rest)), fre_ranges_go(t, rest)) : {Wr.put_list.step(~Dr.Range, ~DocRows.rows.spell_range, x, _) == (1n+List.length(&2, Dr.Range, t), DocRows.rows.spell_range(x, fre_ranges_items(t, rest))) : Nat & String}
      {==}

# a list of ranges is its count, then its items
def fre_ranges_put(+xs: List<&2, Dr.Range>, -rest: String) -> {Wr.put_list(~Dr.Range, ~DocRows.rows.spell_range, xs, rest) == Wr.put_nat(List.length(&2, Dr.Range, xs), fre_ranges_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Dr.Range, ~DocRows.rows.spell_range, xs, rest), (List.length(&2, Dr.Range, xs), fre_ranges_items(xs, rest)), fre_ranges_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Dr.Range, xs), fre_ranges_items(xs, rest)) : String}
  {==}

# what the item loop's answer says about its input s (m + 1 items)
def fre_pll(s: String, m: Nat, d: Wr.Dec<List<&2, Dr.Range>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == fre_ranges_items(xs, r) : String} & ({List.length(&2, Dr.Range, xs) == 1n+m : Nat} & {DocRows.rows.RangesFit(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

# one more spelled range before the rest of the loop
def fre_ranges_step(-s: String, x: Dr.Range, -s3: String, -k: Nat, d: Wr.Dec<List<&2, Dr.Range>>,
  ih: fre_pll(s3, k, d), px: fre_pr(s, Wr.Got{x, s3})) -> fre_pll(s, 1n+k, Wr.get_list.cons(Dr.Range, x, d)):
  match x:
    case Dr.Range{+st, +m}:
      match d:
        case Wr.Got{+ys, +r}:
          (e1, (e2, e3)) = ih
          (ex, fx) = px
          (Equal.trans(String, s, Wr.put_nat(st, DocRows.rows.spell_mnat(m, s3)), Wr.put_nat(st, DocRows.rows.spell_mnat(m, fre_ranges_items(ys, r))), ex,
              Equal.cong(String, String, z => Wr.put_nat(st, DocRows.rows.spell_mnat(m, z)), s3, fre_ranges_items(ys, r), e1)),
            (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Dr.Range, ys), 1n+k, e2),
              Fdx.fdx_and(Bool.and(LawsBase.wire_fits(st), LawsBase.wire_mfits(m)), DocRows.rows.RangesFit(ys), fx, e3)))
        case Wr.Bad{}:
          Unit{}

# the item loop accepts only spelled ranges that fit
def fre_ranges_loop(m: Nat, cur: Wr.Dec<Dr.Range>, +s: String, pc: fre_pr(s, cur)) ->
  fre_pll(s, m, Wr.get_list.go(~Dr.Range, ~Fdr.get_range, m, cur)):
  match m cur:
    case 0n Wr.Got{x, s3}:
      match x:
        case Dr.Range{+st, +mm}:
          (ex, fx) = pc
          (ex, ({==}, Fdx.fdx_and(Bool.and(LawsBase.wire_fits(st), LawsBase.wire_mfits(mm)), True{}, fx, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      fre_ranges_step(s, x, s3, k, Wr.get_list.go(~Dr.Range, ~Fdr.get_range, k, Fdr.get_range(s3)),
        fre_ranges_loop(k, Fdr.get_range(s3), s3, fre_range(s3)), pc)
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list-of-ranges decoder's answer says about its input s
def fre_pls(s: String, d: Wr.Dec<List<&2, Dr.Range>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == Wr.put_list(~Dr.Range, ~DocRows.rows.spell_range, xs, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Range, xs)), DocRows.rows.RangesFit(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# the count spelled before the items is the list's length
def fre_ranges_eq(-s: String, -s2: String, -m: Nat, +xs: List<&2, Dr.Range>, -r: String,
  en: {s == Wr.put_nat(1n+m, s2) : String}, e1: {s2 == fre_ranges_items(xs, r) : String},
  e2: {List.length(&2, Dr.Range, xs) == 1n+m : Nat}) -> {s == Wr.put_list(~Dr.Range, ~DocRows.rows.spell_range, xs, r) : String}:
  %Equal.sym(String, Wr.put_list(~Dr.Range, ~DocRows.rows.spell_range, xs, r), Wr.put_nat(List.length(&2, Dr.Range, xs), fre_ranges_items(xs, r)), fre_ranges_put(xs, r)) : {s == _ : String}
  %Equal.sym(Nat, List.length(&2, Dr.Range, xs), 1n+m, e2) : {s == Wr.put_nat(_, fre_ranges_items(xs, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

# m + 1 spelled ranges after their count: a spelled list that fits
def fre_ranges_conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Dr.Range>>, pl: fre_pll(s2, m, d)) -> fre_pls(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, (+e2, e3)) = pl
      (fre_ranges_eq(s, s2, m, xs, r, en, e1, e2),
        Fdx.fdx_and(LawsBase.wire_fits(List.length(&2, Dr.Range, xs)), DocRows.rows.RangesFit(xs),
          Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, Dr.Range, xs)), LawsBase.wire_fits(1n+m), True{},
            Equal.cong(Nat, Bool, k => LawsBase.wire_fits(k), List.length(&2, Dr.Range, xs), 1n+m, e2), fn), e3))
    case Wr.Bad{}:
      Unit{}

# the count 0 is the empty list; else the item loop runs
def fre_ranges_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String},
  fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> fre_pls(s, Wr.get_list.start(~Dr.Range, ~Fdr.get_range, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, {==})
    case 1n++m:
      fre_ranges_conv(s, s2, m, en, fn, Wr.get_list.go(~Dr.Range, ~Fdr.get_range, m, Fdr.get_range(s2)),
        fre_ranges_loop(m, Fdr.get_range(s2), s2, fre_range(s2)))

# a list starts with a spelled count that fits
def fre_ranges_top(+s: String, d: Wr.Dec<Nat>, pn: Fdx.fdx_pn(s, d)) -> fre_pls(s, Wr.get_list.start(~Dr.Range, ~Fdr.get_range, d)):
  match d:
    case Wr.Got{+n, +s2}:
      (en, fn) = pn
      fre_ranges_nat(s, n, s2, en, fn)
    case Wr.Bad{}:
      Unit{}

# every list of ranges the decoder reads is spelled and fits
def fre_ranges(+s: String) -> fre_pls(s, Wr.get_list(~Dr.Range, ~Fdr.get_range, s)):
  fre_ranges_top(s, Wr.get_nat(s), Fdx.fdx_nat(s))

# ==== a selector ====

# what a selector decoder's answer says about its input s
def fre_ps(s: String, d: Wr.Dec<Dr.Sel>) -> Type:
  match d:
    case Wr.Got{+sel, r}:
      {s == DocRows.rows.spell_sel(sel, r) : String} & {DocRows.rows.SelFits(sel) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# tag 2, spelled ranges, then a spelled raw flag
def fre_sel_raw(-s: String, -s2: String, +xs: List<&2, Dr.Range>, -s3: String, en: {s == Wr.put_nat(2n, s2) : String},
  el: {s2 == Wr.put_list(~Dr.Range, ~DocRows.rows.spell_range, xs, s3) : String},
  fl: {Bool.and(LawsBase.wire_fits(List.length(&2, Dr.Range, xs)), DocRows.rows.RangesFit(xs)) == True{} : Bool},
  d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s3, d)) -> fre_ps(s, Fdr.get_sel.raw(xs, d)):
  match d:
    case Wr.Got{+raw, +s4}:
      (Equal.trans(String, s, Wr.put_nat(2n, s2), Wr.put_nat(2n, Wr.put_list(~Dr.Range, ~DocRows.rows.spell_range, xs, Wr.put_bool(raw, s4))), en,
        Equal.cong(String, String, z => Wr.put_nat(2n, z), s2, Wr.put_list(~Dr.Range, ~DocRows.rows.spell_range, xs, Wr.put_bool(raw, s4)),
          Equal.trans(String, s2, Wr.put_list(~Dr.Range, ~DocRows.rows.spell_range, xs, s3), Wr.put_list(~Dr.Range, ~DocRows.rows.spell_range, xs, Wr.put_bool(raw, s4)), el,
            Equal.cong(String, String, z => Wr.put_list(~Dr.Range, ~DocRows.rows.spell_range, xs, z), s3, Wr.put_bool(raw, s4), pb)))), fl)
    case Wr.Bad{}:
      Unit{}

# tag 2, then spelled ranges that fit, then the raw flag
def fre_sel_ranges(-s: String, -s2: String, en: {s == Wr.put_nat(2n, s2) : String},
  d: Wr.Dec<List<&2, Dr.Range>>, pl: fre_pls(s2, d)) -> fre_ps(s, Fdr.get_sel.ranges(d)):
  match d:
    case Wr.Got{+xs, +s3}:
      (el, fl) = pl
      fre_sel_raw(s, s2, xs, s3, en, el, fl, Wr.get_bool(s3), PWireBoolExact.wr_bool_spec(s3))
    case Wr.Bad{}:
      Unit{}

# the selector tag is 0, 1 or 2 (then ranges and a flag)
def fre_sel_tag(-s: String, d: Wr.Dec<Nat>, pn: Fdx.fdx_pn(s, d)) -> fre_ps(s, Fdr.get_sel.tag(d)):
  match d:
    case Wr.Got{t, +r}:
      match t:
        case 0n:
          (e, f) = pn
          (e, {==})
        case 1n:
          (e, f) = pn
          (e, {==})
        case 2n:
          (e, f) = pn
          fre_sel_ranges(s, r, e, Wr.get_list(~Dr.Range, ~Fdr.get_range, r), fre_ranges(r))
        case 3n+p:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# every selector the decoder reads is spelled and fits
def fre_sel(+s: String) -> fre_ps(s, Fdr.get_sel(s)):
  fre_sel_tag(s, Wr.get_nat(s), Fdx.fdx_nat(s))

# ==== a gate request ====

# four flags with nothing left over
def fre_gate_done(+s6: String, -s: String, +raw: Bool, +u8: Bool, +u16: Bool, +nul: Bool,
  e: {s == Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, Wr.put_bool(nul, s6))))) : String},
  h: {LawsBase.wire_opens_err(Fdr.gate.done(raw, u8, u16, nul, Wr.end(s6))) == False{} : Bool}) -> fre_Ex(s):
  match s6:
    case SNil{}:
      (DocRows.rows.GateReq{raw, u8, u16, nul}, (e, {==}))
    case SCon{ch, t}:
      Fdx.fdx_absurd(fre_Ex(s), h)

# the fourth flag (nul)
def fre_gate_nul(-s: String, +raw: Bool, +u8: Bool, +u16: Bool, -s5: String,
  e: {s == Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, s5)))) : String},
  d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s5, d),
  h: {LawsBase.wire_opens_err(Fdr.gate.nul(raw, u8, u16, d)) == False{} : Bool}) -> fre_Ex(s):
  match d:
    case Wr.Got{+nul, +s6}:
      fre_gate_done(s6, s, raw, u8, u16, nul,
        Equal.trans(String, s, Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, s5)))), Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, Wr.put_bool(nul, s6))))), e,
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, z)))), s5, Wr.put_bool(nul, s6), pb)), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(fre_Ex(s), h)

# the third flag (utf16)
def fre_gate_u16(-s: String, +raw: Bool, +u8: Bool, -s4: String,
  e: {s == Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, s4))) : String},
  d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s4, d),
  h: {LawsBase.wire_opens_err(Fdr.gate.u16(raw, u8, d)) == False{} : Bool}) -> fre_Ex(s):
  match d:
    case Wr.Got{+u16, +s5}:
      fre_gate_nul(s, raw, u8, u16, s5,
        Equal.trans(String, s, Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, s4))), Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, Wr.put_bool(u16, s5)))), e,
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, z))), s4, Wr.put_bool(u16, s5), pb)),
        Wr.get_bool(s5), PWireBoolExact.wr_bool_spec(s5), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(fre_Ex(s), h)

# the second flag (utf8)
def fre_gate_u8(-s: String, +raw: Bool, -s3: String, e: {s == Wr.put_nat(0n, Wr.put_bool(raw, s3)) : String},
  d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s3, d),
  h: {LawsBase.wire_opens_err(Fdr.gate.u8(raw, d)) == False{} : Bool}) -> fre_Ex(s):
  match d:
    case Wr.Got{+u8, +s4}:
      fre_gate_u16(s, raw, u8, s4,
        Equal.trans(String, s, Wr.put_nat(0n, Wr.put_bool(raw, s3)), Wr.put_nat(0n, Wr.put_bool(raw, Wr.put_bool(u8, s4))), e,
          Equal.cong(String, String, z => Wr.put_nat(0n, Wr.put_bool(raw, z)), s3, Wr.put_bool(u8, s4), pb)),
        Wr.get_bool(s4), PWireBoolExact.wr_bool_spec(s4), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(fre_Ex(s), h)

# tag 0, then four spelled flags
def fre_gate_raw(-s: String, -s2: String, en: {s == Wr.put_nat(0n, s2) : String},
  d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s2, d),
  h: {LawsBase.wire_opens_err(Fdr.gate.raw(d)) == False{} : Bool}) -> fre_Ex(s):
  match d:
    case Wr.Got{+raw, +s3}:
      fre_gate_u8(s, raw, s3,
        Equal.trans(String, s, Wr.put_nat(0n, s2), Wr.put_nat(0n, Wr.put_bool(raw, s3)), en,
          Equal.cong(String, String, z => Wr.put_nat(0n, z), s2, Wr.put_bool(raw, s3), pb)),
        Wr.get_bool(s3), PWireBoolExact.wr_bool_spec(s3), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(fre_Ex(s), h)

# ==== a view request ====

# selector, flags and projection with nothing left over
def fre_view_done(+s6: String, -s: String, +sel: Dr.Sel, +u8: Bool, +over: Bool, +p: Dl.Proj,
  e: {s == Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, LawsBase.proj_spell(p, s6))))) : String},
  fs: {DocRows.rows.SelFits(sel) == True{} : Bool}, fp: {LawsBase.proj_fits(p) == True{} : Bool},
  h: {LawsBase.wire_opens_err(Fdr.view.done(sel, u8, over, p, Wr.end(s6))) == False{} : Bool}) -> fre_Ex(s):
  match s6:
    case SNil{}:
      (DocRows.rows.ViewReq{sel, u8, over, p}, (e, Fdx.fdx_and(DocRows.rows.SelFits(sel), LawsBase.proj_fits(p), fs, fp)))
    case SCon{ch, t}:
      Fdx.fdx_absurd(fre_Ex(s), h)

# the projection
def fre_view_proj(-s: String, +sel: Dr.Sel, +u8: Bool, +over: Bool, -s5: String,
  e: {s == Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, s5)))) : String},
  fs: {DocRows.rows.SelFits(sel) == True{} : Bool}, d: Wr.Dec<Dl.Proj>, pp: Fdx.fdx_pp(s5, d),
  h: {LawsBase.wire_opens_err(Fdr.view.proj(sel, u8, over, d)) == False{} : Bool}) -> fre_Ex(s):
  match d:
    case Wr.Got{+p, +s6}:
      (ep, fp) = pp
      fre_view_done(s6, s, sel, u8, over, p,
        Equal.trans(String, s, Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, s5)))), Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, LawsBase.proj_spell(p, s6))))), e,
          Equal.cong(String, String, z => Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, z)))), s5, LawsBase.proj_spell(p, s6), ep)),
        fs, fp, h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(fre_Ex(s), h)

# the over flag
def fre_view_over(-s: String, +sel: Dr.Sel, +u8: Bool, -s4: String,
  e: {s == Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, s4))) : String},
  fs: {DocRows.rows.SelFits(sel) == True{} : Bool}, d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s4, d),
  h: {LawsBase.wire_opens_err(Fdr.view.over(sel, u8, d)) == False{} : Bool}) -> fre_Ex(s):
  match d:
    case Wr.Got{+over, +s5}:
      fre_view_proj(s, sel, u8, over, s5,
        Equal.trans(String, s, Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, s4))), Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, Wr.put_bool(over, s5)))), e,
          Equal.cong(String, String, z => Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, z))), s4, Wr.put_bool(over, s5), pb)),
        fs, Fdl.get_proj(s5), Fdx.fdx_proj(s5), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(fre_Ex(s), h)

# the utf8 flag
def fre_view_u8(-s: String, +sel: Dr.Sel, -s3: String,
  e: {s == Wr.put_nat(1n, DocRows.rows.spell_sel(sel, s3)) : String},
  fs: {DocRows.rows.SelFits(sel) == True{} : Bool}, d: Wr.Dec<Bool>, pb: PWireBoolExact.wr_pb(s3, d),
  h: {LawsBase.wire_opens_err(Fdr.view.u8(sel, d)) == False{} : Bool}) -> fre_Ex(s):
  match d:
    case Wr.Got{+u8, +s4}:
      fre_view_over(s, sel, u8, s4,
        Equal.trans(String, s, Wr.put_nat(1n, DocRows.rows.spell_sel(sel, s3)), Wr.put_nat(1n, DocRows.rows.spell_sel(sel, Wr.put_bool(u8, s4))), e,
          Equal.cong(String, String, z => Wr.put_nat(1n, DocRows.rows.spell_sel(sel, z)), s3, Wr.put_bool(u8, s4), pb)),
        fs, Wr.get_bool(s4), PWireBoolExact.wr_bool_spec(s4), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(fre_Ex(s), h)

# tag 1, then a spelled selector that fits
def fre_view_sel(-s: String, -s2: String, en: {s == Wr.put_nat(1n, s2) : String},
  d: Wr.Dec<Dr.Sel>, ps: fre_ps(s2, d),
  h: {LawsBase.wire_opens_err(Fdr.view.sel(d)) == False{} : Bool}) -> fre_Ex(s):
  match d:
    case Wr.Got{+sel, +s3}:
      (es, fs) = ps
      fre_view_u8(s, sel, s3,
        Equal.trans(String, s, Wr.put_nat(1n, s2), Wr.put_nat(1n, DocRows.rows.spell_sel(sel, s3)), en,
          Equal.cong(String, String, z => Wr.put_nat(1n, z), s2, DocRows.rows.spell_sel(sel, s3), es)),
        fs, Wr.get_bool(s3), PWireBoolExact.wr_bool_spec(s3), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(fre_Ex(s), h)

# ==== the entry ====

# the request tag is 0 (gate) or 1 (view), else an error
def fre_entry(-s: String, d: Wr.Dec<Nat>, pn: Fdx.fdx_pn(s, d),
  h: {LawsBase.wire_opens_err(Fdr.run(d)) == False{} : Bool}) -> fre_Ex(s):
  match d:
    case Wr.Got{t, +s2}:
      match t:
        case 0n:
          (en, fn) = pn
          fre_gate_raw(s, s2, en, Wr.get_bool(s2), PWireBoolExact.wr_bool_spec(s2), h)
        case 1n:
          (en, fn) = pn
          fre_view_sel(s, s2, en, Fdr.get_sel(s2), fre_sel(s2), h)
        case 2n+p:
          Fdx.fdx_absurd(fre_Ex(s), h)
    case Wr.Bad{}:
      Fdx.fdx_absurd(fre_Ex(s), h)

# the law: follow the entry's decoders on s
def DocRows.rows_entry_exact(s, h):
  fre_entry(s, Wr.get_nat(s), Fdx.fdx_nat(s), h)
