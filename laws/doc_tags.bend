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

# LAW tag_names_shown_text: the tag of a read or grep result names the text its rows come
# from: the tag is the identity of that text, and every row (n, x) is
# line n of it
law tag_names_shown_text:
  for +t: List<&2, Nat>
  for +op: Dt.Op
  {Dt.Shown.tag(Dt.show(t, op)) == t : List<&2, Nat>} & {Dt.from_text(t, Dt.Shown.rows(Dt.show(t, op))) == True{} : Bool}

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

# R1
def sp_fate(s: Dt.Scan) -> Dt.Fate:
  match s:
    case Dt.Part{}:
      Dt.OverLimit{}
    case Dt.Whole{u}:
      match u:
        case True{}:
          Dt.Tagged{}
        case False{}:
          Dt.NotUtf8{}

def sp_fates(ss: List<&2, Dt.Scan>) -> List<&2, Dt.Fate>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      sp_fate(s) <> sp_fates(rest)

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

# the reply Rust reads: the spelled choices of the spec
def sp_w_reply(ss: List<&2, Dt.Scan>) -> String:
  Wr.put_list(~Dt.Fate, ~sp_w_fate, sp_fates(ss), "")

# the request's count fits the wire
def sp_fit_req(ss: List<&2, Dt.Scan>) -> Bool:
  LawsBase.wire_fits(List.length(&2, Dt.Scan, ss))

# Laws
# ----

# LAW grep_tag_fates_spec (R1): the choice for each shown file, in order:
# tag a whole UTF-8 file, no tag over the limit or for another encoding
# EXCLUDES: a partly searched file tagged (an edit then works on part of
#   it); a whole UTF-8 file left untagged; an untagged file blamed on the
#   wrong cause; a file lost, added or reordered
law grep_tag_fates_spec:
  for +ss: List<&2, Dt.Scan>
  {Dt.fates(ss) == sp_fates(ss) : List<&2, Dt.Fate>}

# LAW tags_entry_answers (R2): the entry answers every request Rust
# spells, its count within the wire, with the spelled choices of the spec
# EXCLUDES: a scan misread, a file dropped or reordered, a default answer
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
