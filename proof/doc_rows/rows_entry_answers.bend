# eukhe: the proof of LAW rows_entry_answers

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
import ../base/wire.bend as LWire
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../base/ffi_doc_lines/round_trip.bend as LFdlRoundTrip

# ==== the selector reads back ====

# a range's end the spec spells reads back
def rea_mnat_rt(m: Maybe<&2, Nat>, +rest: String, h: {LawsBase.wire_mfits(m) == True{} : Bool}) -> {Fdr.get_mnat(DocRows.rows.spell_mnat(m, rest)) == Wr.Got{m, rest} : Wr.Dec<Maybe<&2, Nat>>}:
  match m:
    case None{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {Fdr.get_mnat.tag(_) == Wr.Got{None{}, rest} : Wr.Dec<Maybe<&2, Nat>>}
      {==}
    case Some{+n}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, Wr.put_nat(n, rest))), Wr.Got{1n, Wr.put_nat(n, rest)}, Wire.wire_nat_round_trip(1n, Wr.put_nat(n, rest), {==})) : {Fdr.get_mnat.tag(_) == Wr.Got{Some{n}, rest} : Wr.Dec<Maybe<&2, Nat>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h)) : {Fdr.get_mnat.some(_) == Wr.Got{Some{n}, rest} : Wr.Dec<Maybe<&2, Nat>>}
      {==}

# a range that fits (the head of a list that fits) reads back
def rea_range_rt(x: Dr.Range, -t: List<&2, Dr.Range>, +rest: String, h: {DocRows.rows.RangesFit(x <> t) == True{} : Bool}) -> {Fdr.get_range(DocRows.rows.spell_range(x, rest)) == Wr.Got{x, rest} : Wr.Dec<Dr.Range>}:
  match x:
    case Dr.Range{+st, +m}:
      +hx = LLogicBool.wr_and_l(Bool.and(LawsBase.wire_fits(st), LawsBase.wire_mfits(m)), DocRows.rows.RangesFit(t), h)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(st, DocRows.rows.spell_mnat(m, rest))), Wr.Got{st, DocRows.rows.spell_mnat(m, rest)}, Wire.wire_nat_round_trip(st, DocRows.rows.spell_mnat(m, rest), LLogicBool.wr_and_l(LawsBase.wire_fits(st), LawsBase.wire_mfits(m), hx))) : {Fdr.get_range.start(_) == Wr.Got{Dr.Range{st, m}, rest} : Wr.Dec<Dr.Range>}
      %Equal.sym(Wr.Dec<Maybe<&2, Nat>>, Fdr.get_mnat(DocRows.rows.spell_mnat(m, rest)), Wr.Got{m, rest}, rea_mnat_rt(m, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(st), LawsBase.wire_mfits(m), hx))) : {Fdr.get_range.end(st, _) == Wr.Got{Dr.Range{st, m}, rest} : Wr.Dec<Dr.Range>}
      {==}

# the tail of a list of ranges that fits fits
def rea_fit_tail(x: Dr.Range, -t: List<&2, Dr.Range>, h: {DocRows.rows.RangesFit(x <> t) == True{} : Bool}) -> {DocRows.rows.RangesFit(t) == True{} : Bool}:
  match x:
    case Dr.Range{+st, +m}:
      LLogicBool.wr_and_r(Bool.and(LawsBase.wire_fits(st), LawsBase.wire_mfits(m)), DocRows.rows.RangesFit(t), h)

# the items the spec spells for a list of ranges, then rest
def rea_items(xs: List<&2, Dr.Range>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      DocRows.rows.spell_range(x, rea_items(t, rest))

# the list loop of the spec speller is the count and the items
def rea_go(xs: List<&2, Dr.Range>, -rest: String) -> {Wr.put_list.go(~Dr.Range, ~DocRows.rows.spell_range, xs, rest) == (List.length(&2, Dr.Range, xs), rea_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~Dr.Range, ~DocRows.rows.spell_range, t, rest), (List.length(&2, Dr.Range, t), rea_items(t, rest)), rea_go(t, rest)) : {Wr.put_list.step(~Dr.Range, ~DocRows.rows.spell_range, x, _) == (1n+List.length(&2, Dr.Range, t), DocRows.rows.spell_range(x, rea_items(t, rest))) : Nat & String}
      {==}

# the spec spelling of a list of ranges is its count, then its items
def rea_put(+xs: List<&2, Dr.Range>, -rest: String) -> {Wr.put_list(~Dr.Range, ~DocRows.rows.spell_range, xs, rest) == Wr.put_nat(List.length(&2, Dr.Range, xs), rea_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Dr.Range, ~DocRows.rows.spell_range, xs, rest), (List.length(&2, Dr.Range, xs), rea_items(xs, rest)), rea_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, Dr.Range, xs), rea_items(xs, rest)) : String}
  {==}

# the decoder's loop reads back the items of a list that fits
def rea_loop(+t: List<&2, Dr.Range>, +x: Dr.Range, +rest: String, +hf: {DocRows.rows.RangesFit(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~Dr.Range, ~Fdr.get_range, List.length(&2, Dr.Range, t), Fdr.get_range(DocRows.rows.spell_range(x, rea_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Dr.Range>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<Dr.Range>, Fdr.get_range(DocRows.rows.spell_range(x, rest)), Wr.Got{x, rest}, rea_range_rt(x, Nil{}, rest, hf)) : {Wr.get_list.go(~Dr.Range, ~Fdr.get_range, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, Dr.Range>>}
      {==}
    case Con{+y, +u}:
      +r2 = DocRows.rows.spell_range(y, rea_items(u, rest))
      %Equal.sym(Wr.Dec<Dr.Range>, Fdr.get_range(DocRows.rows.spell_range(x, r2)), Wr.Got{x, r2}, rea_range_rt(x, y <> u, r2, hf)) : {Wr.get_list.go(~Dr.Range, ~Fdr.get_range, 1n+List.length(&2, Dr.Range, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dr.Range>>}
      %Equal.sym(Wr.Dec<List<&2, Dr.Range>>, Wr.get_list.go(~Dr.Range, ~Fdr.get_range, List.length(&2, Dr.Range, u), Fdr.get_range(r2)), Wr.Got{y <> u, rest}, rea_loop(u, y, rest, rea_fit_tail(x, y <> u, hf))) : {Wr.get_list.cons(Dr.Range, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, Dr.Range>>}
      {==}

# a list of ranges that fits reads back
def rea_ranges(+xs: List<&2, Dr.Range>, +rest: String, hl: {LawsBase.wire_fits(List.length(&2, Dr.Range, xs)) == True{} : Bool}, hi: {DocRows.rows.RangesFit(xs) == True{} : Bool}) -> {Wr.get_list(~Dr.Range, ~Fdr.get_range, Wr.put_list(~Dr.Range, ~DocRows.rows.spell_range, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Dr.Range>>}:
  match xs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, hl)) : {Wr.get_list.start(~Dr.Range, ~Fdr.get_range, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, Dr.Range>>}
      {==}
    case Con{+x, +t}:
      +items = rea_items(x <> t, rest)
      %Equal.sym(String, Wr.put_list(~Dr.Range, ~DocRows.rows.spell_range, x <> t, rest), Wr.put_nat(List.length(&2, Dr.Range, x <> t), items), rea_put(x <> t, rest)) : {Wr.get_list(~Dr.Range, ~Fdr.get_range, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Dr.Range>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, Dr.Range, x <> t), items)), Wr.Got{List.length(&2, Dr.Range, x <> t), items}, Wire.wire_nat_round_trip(List.length(&2, Dr.Range, x <> t), items, hl)) : {Wr.get_list.start(~Dr.Range, ~Fdr.get_range, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, Dr.Range>>}
      rea_loop(t, x, rest, hi)

# a selector whose numbers fit reads back
def rea_sel_rt(s: Dr.Sel, +rest: String, +h: {DocRows.rows.SelFits(s) == True{} : Bool}) -> {Fdr.get_sel(DocRows.rows.spell_sel(s, rest)) == Wr.Got{s, rest} : Wr.Dec<Dr.Sel>}:
  match s:
    case Dr.Whole{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, {==})) : {Fdr.get_sel.tag(_) == Wr.Got{Dr.Whole{}, rest} : Wr.Dec<Dr.Sel>}
      {==}
    case Dr.Raw{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, rest)), Wr.Got{1n, rest}, Wire.wire_nat_round_trip(1n, rest, {==})) : {Fdr.get_sel.tag(_) == Wr.Got{Dr.Raw{}, rest} : Wr.Dec<Dr.Sel>}
      {==}
    case Dr.Lines{+xs, +raw}:
      +tail = Wr.put_bool(raw, rest)
      +body = Wr.put_list(~Dr.Range, ~DocRows.rows.spell_range, xs, tail)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(2n, body)), Wr.Got{2n, body}, Wire.wire_nat_round_trip(2n, body, {==})) : {Fdr.get_sel.tag(_) == Wr.Got{Dr.Lines{xs, raw}, rest} : Wr.Dec<Dr.Sel>}
      %Equal.sym(Wr.Dec<List<&2, Dr.Range>>, Wr.get_list(~Dr.Range, ~Fdr.get_range, body), Wr.Got{xs, tail}, rea_ranges(xs, tail, LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, Dr.Range, xs)), DocRows.rows.RangesFit(xs), h), LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, Dr.Range, xs)), DocRows.rows.RangesFit(xs), h))) : {Fdr.get_sel.ranges(_) == Wr.Got{Dr.Lines{xs, raw}, rest} : Wr.Dec<Dr.Sel>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(tail), Wr.Got{raw, rest}, Wire.wire_bool_round_trip(raw, rest)) : {Fdr.get_sel.raw(xs, _) == Wr.Got{Dr.Lines{xs, raw}, rest} : Wr.Dec<Dr.Sel>}
      {==}

# ==== the replies are the spec's spellings ====

# a gate: put_gate is the spec's
def rea_gate(g: Dr.Gate) -> {Fdr.put_gate(g) == DocRows.rows.spell_gate(g) : String}:
  match g:
    case Dr.Go{}:
      {==}
    case Dr.NotUtf8{}:
      {==}
    case Dr.Binary{}:
      {==}

# a span: put_span is the spec's
def rea_span1(x: Dr.Span, -rest: String) -> {Fdr.put_span(x, rest) == DocRows.rows.spell_span(x, rest) : String}:
  match x:
    case Dr.Span{s, e, g}:
      {==}

# one step of the list loop over spans: put_span is the spec's
def rea_span_step(x: Dr.Span, r: Nat & String) -> {Wr.put_list.step(~Dr.Span, ~Fdr.put_span, x, r) == Wr.put_list.step(~Dr.Span, ~DocRows.rows.spell_span, x, r) : Nat & String}:
  match r:
    case (n, s):
      %rea_span1(x, s) : {(1n+n, Fdr.put_span(x, s)) == (1n+n, _) : Nat & String}
      {==}

# the list loop over spans: put_span is the spec's
def rea_spans_go(xs: List<&2, Dr.Span>, +rest: String) -> {Wr.put_list.go(~Dr.Span, ~Fdr.put_span, xs, rest) == Wr.put_list.go(~Dr.Span, ~DocRows.rows.spell_span, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %rea_spans_go(t, rest) : {Wr.put_list.step(~Dr.Span, ~Fdr.put_span, x, Wr.put_list.go(~Dr.Span, ~Fdr.put_span, t, rest)) == Wr.put_list.step(~Dr.Span, ~DocRows.rows.spell_span, x, _) : Nat & String}
      rea_span_step(x, Wr.put_list.go(~Dr.Span, ~Fdr.put_span, t, rest))

# a list of spans: the codec's spelling is the spec's
def rea_spans(xs: List<&2, Dr.Span>, +rest: String) -> {Wr.put_list(~Dr.Span, ~Fdr.put_span, xs, rest) == Wr.put_list(~Dr.Span, ~DocRows.rows.spell_span, xs, rest) : String}:
  %rea_spans_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~Dr.Span, ~Fdr.put_span, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

# a notice: put_note is the spec's
def rea_note1(x: Dr.Note, -rest: String) -> {Fdr.put_note(x, rest) == DocRows.rows.spell_note(x, rest) : String}:
  match x:
    case Dr.Beyond{l}:
      {==}
    case Dr.Remain{c, y}:
      {==}
    case Dr.RangeBeyond{s, m}:
      match m:
        case None{}:
          {==}
        case Some{e}:
          {==}
    case Dr.TooBig{}:
      {==}

# one step of the list loop over notices: put_note is the spec's
def rea_note_step(x: Dr.Note, r: Nat & String) -> {Wr.put_list.step(~Dr.Note, ~Fdr.put_note, x, r) == Wr.put_list.step(~Dr.Note, ~DocRows.rows.spell_note, x, r) : Nat & String}:
  match r:
    case (n, s):
      %rea_note1(x, s) : {(1n+n, Fdr.put_note(x, s)) == (1n+n, _) : Nat & String}
      {==}

# the list loop over notices: put_note is the spec's
def rea_notes_go(xs: List<&2, Dr.Note>, +rest: String) -> {Wr.put_list.go(~Dr.Note, ~Fdr.put_note, xs, rest) == Wr.put_list.go(~Dr.Note, ~DocRows.rows.spell_note, xs, rest) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %rea_notes_go(t, rest) : {Wr.put_list.step(~Dr.Note, ~Fdr.put_note, x, Wr.put_list.go(~Dr.Note, ~Fdr.put_note, t, rest)) == Wr.put_list.step(~Dr.Note, ~DocRows.rows.spell_note, x, _) : Nat & String}
      rea_note_step(x, Wr.put_list.go(~Dr.Note, ~Fdr.put_note, t, rest))

# a list of notices: the codec's spelling is the spec's
def rea_notes(xs: List<&2, Dr.Note>, +rest: String) -> {Wr.put_list(~Dr.Note, ~Fdr.put_note, xs, rest) == Wr.put_list(~Dr.Note, ~DocRows.rows.spell_note, xs, rest) : String}:
  %rea_notes_go(xs, rest) : {Wr.put_list.fin(Wr.put_list.go(~Dr.Note, ~Fdr.put_note, xs, rest)) == Wr.put_list.fin(_) : String}
  {==}

# what a read shows: put_view is the spec's
def rea_view(v: Dr.View) -> {Fdr.put_view(v) == DocRows.rows.spell_view(v) : String}:
  match v:
    case Dr.View{t, raw, +sp, +ns, +tag}:
      +lhs = Wr.put_nat(t, Wr.put_bool(raw, Wr.put_list(~Dr.Span, ~Fdr.put_span, sp, Wr.put_list(~Dr.Note, ~Fdr.put_note, ns, Wr.put_bool(tag, "")))))
      %rea_notes(ns, Wr.put_bool(tag, "")) : {lhs == Wr.put_nat(t, Wr.put_bool(raw, Wr.put_list(~Dr.Span, ~DocRows.rows.spell_span, sp, _))) : String}
      %rea_spans(sp, Wr.put_list(~Dr.Note, ~Fdr.put_note, ns, Wr.put_bool(tag, ""))) : {lhs == Wr.put_nat(t, Wr.put_bool(raw, _)) : String}
      {==}

# ==== the requests ====

# a gate: the tag and four Bools read back, the gate is spelled
def rea_gate_req(+raw: Bool, +u8: Bool, +u16: Bool, +nul: Bool) -> {Fdr.ffi(DocRows.rows.spell_req(DocRows.rows.GateReq{raw, u8, u16, nul})) == DocRows.rows.answer(DocRows.rows.GateReq{raw, u8, u16, nul}) : String}:
  +s4 = Wr.put_bool(nul, "")
  +s3 = Wr.put_bool(u16, s4)
  +s2 = Wr.put_bool(u8, s3)
  +s1 = Wr.put_bool(raw, s2)
  +ans = DocRows.rows.spell_gate(Dr.gate(raw, u8, u16, nul))
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, s1)), Wr.Got{0n, s1}, Wire.wire_nat_round_trip(0n, s1, {==})) : {Fdr.run(_) == ans : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(s1), Wr.Got{raw, s2}, Wire.wire_bool_round_trip(raw, s2)) : {Fdr.gate.raw(_) == ans : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(s2), Wr.Got{u8, s3}, Wire.wire_bool_round_trip(u8, s3)) : {Fdr.gate.u8(raw, _) == ans : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(s3), Wr.Got{u16, s4}, Wire.wire_bool_round_trip(u16, s4)) : {Fdr.gate.u16(raw, u8, _) == ans : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(s4), Wr.Got{nul, ""}, Wire.wire_bool_round_trip(nul, "")) : {Fdr.gate.nul(raw, u8, u16, _) == ans : String}
  rea_gate(Dr.gate(raw, u8, u16, nul))

# a view: the tag, the selector, two Bools and the projection read back,
# what the read shows is spelled
def rea_view_req(+sel: Dr.Sel, +u8: Bool, +over: Bool, +p: Dl.Proj, +h: {Bool.and(DocRows.rows.SelFits(sel), LawsBase.proj_fits(p)) == True{} : Bool}) -> {Fdr.ffi(DocRows.rows.spell_req(DocRows.rows.ViewReq{sel, u8, over, p})) == DocRows.rows.answer(DocRows.rows.ViewReq{sel, u8, over, p}) : String}:
  +s3 = LawsBase.proj_spell(p, "")
  +s2 = Wr.put_bool(over, s3)
  +s1 = Wr.put_bool(u8, s2)
  +s0 = DocRows.rows.spell_sel(sel, s1)
  +ans = DocRows.rows.spell_view(Dr.view(sel, u8, over, p))
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(1n, s0)), Wr.Got{1n, s0}, Wire.wire_nat_round_trip(1n, s0, {==})) : {Fdr.run(_) == ans : String}
  %Equal.sym(Wr.Dec<Dr.Sel>, Fdr.get_sel(s0), Wr.Got{sel, s1}, rea_sel_rt(sel, s1, LLogicBool.wr_and_l(DocRows.rows.SelFits(sel), LawsBase.proj_fits(p), h))) : {Fdr.view.sel(_) == ans : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(s1), Wr.Got{u8, s2}, Wire.wire_bool_round_trip(u8, s2)) : {Fdr.view.u8(sel, _) == ans : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(s2), Wr.Got{over, s3}, Wire.wire_bool_round_trip(over, s3)) : {Fdr.view.over(sel, u8, _) == ans : String}
  %Equal.sym(Wr.Dec<Dl.Proj>, Fdl.get_proj(s3), Wr.Got{p, ""}, LFdlRoundTrip.fdlrt_proj(p, "", LLogicBool.wr_and_r(DocRows.rows.SelFits(sel), LawsBase.proj_fits(p), h))) : {Fdr.view.proj(sel, u8, over, _) == ans : String}
  rea_view(Dr.view(sel, u8, over, p))

def DocRows.rows_entry_answers(r, h):
  match r:
    case DocRows.rows.GateReq{raw, u8, u16, nul}:
      rea_gate_req(raw, u8, u16, nul)
    case DocRows.rows.ViewReq{sel, u8, over, p}:
      rea_view_req(sel, u8, over, p, h)
