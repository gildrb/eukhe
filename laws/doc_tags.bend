# eukhe: the laws of area doc_tags

import Base
import ../bend/doc_tags.bend as Dt
import ../bend/ffi_doc_tags.bend as FDt
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (F3) Tags
# ---------
# bend/doc_tags.bend: every input is free: any text, any lines shown, a
# read or a grep, and any text the file holds when grep records its
# result.
#
# R3 (tag): a read or grep result is tagged with the exact text it read;
#     grep's with the buffer it searched, never with what the file holds
#     when grep records the result (`later`).
# R4 (rows): a result shows the rows (n, x) of the lines its selection
#     marks, in text order, n the line's number counted from 1; a line
#     with no flag (the selection too short) and a flag with no line (the
#     text too short) show nothing.
# R5 (lines): `is_line(t, n, x)` says line n of t (1 first) is x: there
#     is no line 0 and no line past the end; `from_text(t, rs)` says every
#     row (n, x) of rs is line n of t.

# LAW tag_names_shown_text (R3, R4, R5): the tag of a read or grep result
# names the text its rows come from: the tag is the identity of that
# text, and every row (n, x) is line n of it
law tag_names_shown_text:
  for +t: List<&2, Nat>
  for +op: Dt.Op
  {Dt.Shown.tag(Dt.show(t, op)) == t : List<&2, Nat>} & {Dt.from_text(t, Dt.Shown.rows(Dt.show(t, op))) == True{} : Bool}

# LAW tag_rows_cut (R4): the rows of a text are cut piece by piece: for a
# text ts ++ us under a selection sel ++ tel, sel exactly as long as ts,
# the rows of ts under sel numbered from n, then the rows of us under tel
# numbered on from n + |ts|; one line x selected is the one row (n, x),
# unselected no row; no text, or no selection, cuts no row
# EXCLUDES: a selected line dropped, an unselected one shown, rows
#   reordered, a number that does not count every line before it (also
#   the unselected ones), a row with another line's text, rows past the
#   end of the selection or of the text
law tag_rows_cut:
  for +ts: List<&2, Nat>
  for +us: List<&2, Nat>
  for +sel: List<&2, Bool>
  for +tel: List<&2, Bool>
  for +n: Nat
  for +x: Nat
  for h: {List.length(&2, Bool, sel) == List.length(&2, Nat, ts) : Nat}
  {Dt.rows(List.append(&2, Nat, ts, us), List.append(&2, Bool, sel, tel), n) == List.append(&2, Dt.Row, Dt.rows(ts, sel, n), Dt.rows(us, tel, Nat.add(n, List.length(&2, Nat, ts)))) : List<&2, Dt.Row>} & {[Dt.rows([x], [True{}], n), Dt.rows([x], [False{}], n), Dt.rows(Nil{}, sel, n), Dt.rows(ts, Nil{}, n)] == [[Dt.Row{n, x}], Nil{}, Nil{}, Nil{}] : List<&2, List<&2, Dt.Row>>}

# LAW tag_show_reads (R3, R4): a grep's result is the read's result of the
# same text and selection, whatever the file holds later; a read's result
# is tagged with the text it read and shows the rows of its selection
# numbered from 1 (tag_rows_cut pins those rows)
# EXCLUDES: a grep tagged or cut from `later`; rows numbered from 0; a
#   read and a grep cut differently; a result tagged with another text
law tag_show_reads:
  for +t: List<&2, Nat>
  for +sel: List<&2, Bool>
  for later: List<&2, Nat>
  {Dt.show(t, Dt.Grep{sel, later}) == Dt.show(t, Dt.Read{sel}) : Dt.Shown} & {Dt.show(t, Dt.Read{sel}) == Dt.Shown{t, Dt.rows(t, sel, 1n)} : Dt.Shown}

# LAW tag_line_at (R5): in a text xs ++ [x] ++ ys, line 1 + |xs| is x and
# no other value: `is_line` there answers whether y is x, for every y
# EXCLUDES: a line counted from 0, a line read at another index, any value
#   accepted, a constant answer
law tag_line_at:
  for +xs: List<&2, Nat>
  for +x: Nat
  for +ys: List<&2, Nat>
  for +y: Nat
  {Dt.is_line(List.append(&2, Nat, xs, x <> ys), 1n+List.length(&2, Nat, xs), y) == Nat.is_eq(x, y) : Bool}

# LAW tag_line_outside (R5): there is no line 0, and no line n past the
# end of the text (n above its length), whatever value is asked
# EXCLUDES: line 0 read as the first line, a line past the end accepted
law tag_line_outside:
  for +t: List<&2, Nat>
  for +n: Nat
  for +x: Nat
  for h: {Nat.is_lt(List.length(&2, Nat, t), n) == True{} : Bool}
  {(Dt.is_line(t, 0n, x), Dt.is_line(t, n, x)) == (False{}, False{}) : Bool & Bool}

# LAW tag_from_text_rows (R5): rows are from a text exactly when each of
# them is: no rows are; rows rs ++ qs are exactly when rs are and qs are;
# one row (n, x) is exactly when line n of the text is x
# EXCLUDES: `from_text = True` (which makes tag_names_shown_text vacuous);
#   a check of the first row only; a row off by one line accepted
law tag_from_text_rows:
  for +t: List<&2, Nat>
  for +rs: List<&2, Dt.Row>
  for +qs: List<&2, Dt.Row>
  for +n: Nat
  for +x: Nat
  {Dt.from_text(t, List.append(&2, Dt.Row, rs, qs)) == Bool.and(Dt.from_text(t, rs), Dt.from_text(t, qs)) : Bool} & {(Dt.from_text(t, Nil{}), Dt.from_text(t, [Dt.Row{n, x}])) == (True{}, Dt.is_line(t, n, x)) : Bool & Bool}

# (F3) Grep's tags
# ----------------
# bend/doc_tags.bend `fates`, run as the compiled core by
# bend/ffi_doc_tags.bend (crates/eukhe-docs/src/grep/mod.rs). Every input
# is free: any page of shown files, each searched whole or in part, UTF-8
# or not.
#
# R1: grep tags a shown file exactly when it searched the whole file and
#     its bytes are UTF-8 (the tag is then the searched text's: Rust
#     records what it searched, tag_names_shown_text); a file searched in
#     part has no tag because it is over the limit, one not UTF-8 because
#     of its encoding; one answer per file, in order.
# R2: the entry answers each request Rust writes with the choices of R1,
#     reads exactly the request and nothing after it, and answers any
#     other input with the exact error form.

# Spec helpers
# ------------

# The spelling of a request and of its reply, from the wire primitives
# (R2): a list of scans (Part: 0; Whole: 1 and the UTF-8 flag), a list of
# fates (their tags).

def sp_w_scan(s: Dt.Scan, rest: String) -> String:
  match s:
    case Dt.Part{}:
      Wr.put_nat(0n, rest)
    case Dt.Whole{u}:
      Wr.put_nat(1n, Wr.put_bool(u, rest))

def sp_w_req(ss: List<&2, Dt.Scan>, rest: String) -> String:
  Wr.put_list(~Dt.Scan, ~sp_w_scan, ss, rest)

def sp_w_fate(f: Dt.Fate, rest: String) -> String:
  match f:
    case Dt.Tagged{}:
      Wr.put_nat(0n, rest)
    case Dt.OverLimit{}:
      Wr.put_nat(1n, rest)
    case Dt.NotUtf8{}:
      Wr.put_nat(2n, rest)

# the reply Rust reads: the spelled choices of `fates` (grep_tag_fates
# pins them to R1)
def sp_w_reply(ss: List<&2, Dt.Scan>) -> String:
  Wr.put_list(~Dt.Fate, ~sp_w_fate, Dt.fates(ss), "")

# the request's count fits the wire
def sp_fit_req(ss: List<&2, Dt.Scan>) -> Bool:
  LawsBase.wire_fits(List.length(&2, Dt.Scan, ss))

# Laws
# ----

# LAW grep_tag_fates (R1): a page's choices are its files' choices, one
# each, in order (the choices of ss ++ tt are those of ss then those of
# tt; no file, no choice); a file searched in part is over the limit, a
# whole UTF-8 file is tagged, a whole file of another encoding is not
# UTF-8
# EXCLUDES: a partly searched file tagged (an edit then works on part of
#   it); a whole UTF-8 file left untagged; an untagged file blamed on the
#   wrong cause; a file lost, added or reordered; a choice that depends on
#   another file of the page
law grep_tag_fates:
  for +ss: List<&2, Dt.Scan>
  for +tt: List<&2, Dt.Scan>
  {Dt.fates(List.append(&2, Dt.Scan, ss, tt)) == List.append(&2, Dt.Fate, Dt.fates(ss), Dt.fates(tt)) : List<&2, Dt.Fate>} & {[Dt.fates(Nil{}), Dt.fates([Dt.Part{}]), Dt.fates([Dt.Whole{True{}}]), Dt.fates([Dt.Whole{False{}}])] == [Nil{}, [Dt.OverLimit{}], [Dt.Tagged{}], [Dt.NotUtf8{}]] : List<&2, List<&2, Dt.Fate>>}

# LAW tags_entry_answers (R2): the entry answers every request Rust
# spells, its count within the wire, with the spelled choices of `fates`
# for its scans (grep_tag_fates pins those choices to R1)
# EXCLUDES: a scan misread, a file dropped or reordered, a default answer,
#   an answer other than `fates` of the request
law tags_entry_answers:
  for +ss: List<&2, Dt.Scan>
  for h: {sp_fit_req(ss) == True{} : Bool}
  {FDt.ffi(sp_w_req(ss, "")) == sp_w_reply(ss) : String}

# LAW tags_entry_reads (R2): the entry's decoder reads a spelled request
# back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law tags_entry_reads:
  for +ss: List<&2, Dt.Scan>
  for +rest: String
  for h: {sp_fit_req(ss) == True{} : Bool}
  {FDt.get_req(sp_w_req(ss, rest)) == Wr.Got{ss, rest} : Wr.Dec<List<&2, Dt.Scan>>}

# LAW tags_entry_exact (R2): every input the entry does not answer with
# the error form is a spelled request that fits the wire
# EXCLUDES: a choice made on input that is no request (an unknown tag, a
#   malformed flag, input left over)
law tags_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FDt.ffi(s)) == False{} : Bool}
  exs r: List<&2, Dt.Scan>
  {s == sp_w_req(r, "") : String} & {sp_fit_req(r) == True{} : Bool}

# LAW tags_entry_refuses (R2): every error the entry answers is exactly
# `E doc_tags: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law tags_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FDt.ffi(s)) == True{} : Bool}
  {FDt.ffi(s) == Wr.err("doc_tags: malformed request") : String}

# LAW tags_entry_example (R2): anchor: a page of a whole UTF-8 file, one
# searched in part and one not UTF-8; an empty page; an unknown scan and
# input left over
# EXCLUDES: tags in another order, a field order other than Rust's
law tags_entry_example:
  {[FDt.ffi("3,1,T0,1,F"), FDt.ffi("0,"), FDt.ffi("1,2,"), FDt.ffi("1,0,0,")] == ["3,0,1,2,", "0,", Wr.err("doc_tags: malformed request"), Wr.err("doc_tags: malformed request")] : List<&2, String>}
