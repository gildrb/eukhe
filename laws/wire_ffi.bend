# eukhe: the laws of area wire_ffi

import Base
import ../bend/ffi_wire.bend as FWi
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (B2) The wire round trip
# ------------------------
# bend/ffi_wire.bend, entry 1 of the compiled Bend core: no rule of eukhe,
# the Rust test of crates/eukhe-bend wire.rs (`bend_reads_back_what_rust_writes`,
# `bend_refuses_malformed_requests`) that Bend reads the grammar Rust writes.
# Every input is free.
#
# W1: a request is a Nat, a U32, a Bool, a String and a list of Nats, in
#     that order, spelled by the wire's primitives (laws/wire.bend); on each
#     one whose numbers and lengths fit the wire the entry answers the
#     request itself, byte for byte.
# W2: any other input (a malformed or too long field, an unknown Bool char,
#     a short string, a count past the items, input left over) answers
#     exactly the error form "malformed wire request".

# Spec helpers
# ------------

# a request of the round trip
type wr.Req is Data:
  wr.Req{n: Nat, x: U32, b: Bool, a: String, xs: List<&2, Nat>}

# W1: the spelling of q, then rest
def wr_spell(q: wr.Req, rest: String) -> String:
  match q:
    case wr.Req{n, x, b, a, xs}:
      Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, Wr.put_str(a, LawsBase.wire_spell_nats(xs, rest)))))

# W1: every number and length of q fits the wire
def wr_fits(q: wr.Req) -> Bool:
  match q:
    case wr.Req{n, x, b, +a, +xs}:
      Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(String.length(a)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))))

# Laws
# ----

# LAW wire_ffi_answers (W1): a request spelled by the grammar, every
# number and length within the wire, answers itself, byte for byte
# EXCLUDES: a field lost, swapped, misread, re-spelled or defaulted on the
#   way back; a reply in another order or spelling
law wire_ffi_answers:
  for +q: wr.Req
  for fits: {wr_fits(q) == True{} : Bool}
  {FWi.ffi(wr_spell(q, "")) == wr_spell(q, "") : String}

# LAW wire_ffi_reads_only_requests (W1, W2): an answer that is not the
# error form answers a request: the input is exactly the spelling of a
# request that fits the wire, and the answer is that spelling
# EXCLUDES: a decoder that accepts a malformed or too long field, an
#   unknown Bool char, a short string, a missing item or input left over,
#   and answers it anyway (a value instead of the error form)
law wire_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FWi.ffi(s)) == False{} : Bool}
  exs q: wr.Req
  {(s, (wr_fits(q), FWi.ffi(s))) == (wr_spell(q, ""), (True{}, wr_spell(q, ""))) : String & (Bool & String)}

# LAW wire_ffi_refuses (W2): every error the entry answers is exactly
# `E malformed wire request`
# EXCLUDES: an error text that varies with the input or the field, a
#   second error form
law wire_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FWi.ffi(s)) == True{} : Bool}
  {FWi.ffi(s) == Wr.err("malformed wire request") : String}

# LAW wire_ffi_example (W1, W2): anchor: Rust's vectors (wire.rs): the
# zero request and 42, 7, True, "héllo", [1, 22, 333] answer themselves;
# the empty input, a leading zero, a Bool char X, a short string, a count
# past the items and input left over are refused (the vectors past 2^32 or
# with 15 digits are left to wire_u32_exact and wire_nat_decoded_fits: the
# checker builds them digit by digit)
# EXCLUDES: a spec that drifts from the bytes Rust writes and reads
law wire_ffi_example:
  {[FWi.ffi("0,0,F0,0,"), FWi.ffi("42,7,T5,héllo3,1,22,333,"), FWi.ffi(""), FWi.ffi("01,0,T0,0,"), FWi.ffi("1,1,X0,0,"), FWi.ffi("1,1,T3,ab0,"), FWi.ffi("1,1,T0,2,1,"), FWi.ffi("1,1,T0,0,x")] == ["0,0,F0,0,", "42,7,T5,héllo3,1,22,333,", "E malformed wire request", "E malformed wire request", "E malformed wire request", "E malformed wire request", "E malformed wire request", "E malformed wire request"] : List<&2, String>}

# LAW wire_ffi_fits_witness: witness: requests that fit the wire exist
# EXCLUDES: a vacuous wire_ffi_answers
law wire_ffi_fits_witness:
  {wr_fits(wr.Req{42n, 7, True{}, "héllo", [1n, 22n, 333n]}) == True{} : Bool}
