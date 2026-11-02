# eukhe: the laws of area wire_entry

import Base
import ../bend/ffi_wire.bend as FW
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (W1) The wire round trip through the compiled core
# --------------------------------------------------
# bend/ffi_wire.bend (entry `wire`), the Rust test of crates/eukhe-bend
# (src/wire.rs: bend_reads_back_what_rust_writes,
# bend_refuses_malformed_requests). Every input is free: any text.
#
# R1: a request is a Nat, a U32, a Bool, a String and a List of Nats, each
#     spelled as Rust writes it (LawsBase's decimal spellers: wire_dec,
#     wire_bool_char, wire_dec_str, wire_dec_nats), with nothing after it;
#     the reply is the request itself: Bend reads back exactly what Rust
#     wrote and writes it again byte for byte.
# R2: every other input (a malformed field, a value past the wire, input
#     left over) answers exactly the error form `E malformed wire request`.

# Spec helpers
# ------------

# R1: the request of the values n, x, b, a, xs, then rest, spelled by the
# spec's decimal spellers (never the entry's encoders)
def wire_entry_spell(+n: Nat, +x: U32, b: Bool, +a: String, +xs: List<&2, Nat>, rest: String) -> String:
  LawsBase.wire_dec(n, LawsBase.wire_dec(U32.to_nat(x), SCon{LawsBase.wire_bool_char(b), LawsBase.wire_dec_str(a, LawsBase.wire_dec_nats(xs, rest))}))

# R1: the values fit the wire: the Nat, the string's length, the list's
# count and every item have at most 14 digits (every U32 fits)
def wire_entry_fits(+n: Nat, +a: String, +xs: List<&2, Nat>) -> Bool:
  Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(String.length(a)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))))

# Laws
# ----

# LAW wire_entry_echoes (R1): every request Rust spells, with values that
# fit the wire, is answered with itself
# EXCLUDES: a field misread or rewritten (a digit, a length, a Bool char, a
#   list item), a field lost, added or reordered, a reply in another
#   spelling than the request's
law wire_entry_echoes:
  for +n: Nat
  for +x: U32
  for +b: Bool
  for +a: String
  for +xs: List<&2, Nat>
  for h: {wire_entry_fits(n, a, xs) == True{} : Bool}
  {FW.ffi(wire_entry_spell(n, x, b, a, xs, "")) == wire_entry_spell(n, x, b, a, xs, "") : String}

# LAW wire_entry_exact (R1, R2): every input the entry does not answer with
# the error form is a spelled request of values that fit the wire, with
# nothing after it
# EXCLUDES: a value answered for input that is no request (a malformed
#   field, a 15-digit number, a short list or string, input left over)
law wire_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FW.ffi(s)) == False{} : Bool}
  exs n: Nat
  exs x: U32
  exs b: Bool
  exs a: String
  exs xs: List<&2, Nat>
  {s == wire_entry_spell(n, x, b, a, xs, "") : String} & {wire_entry_fits(n, a, xs) == True{} : Bool}

# LAW wire_entry_refuses (R2): every error the entry answers is exactly
# `E malformed wire request`
# EXCLUDES: an error text that varies with the input, a second error form
law wire_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FW.ffi(s)) == True{} : Bool}
  {FW.ffi(s) == Wr.err("malformed wire request") : String}

# LAW wire_entry_example (R1, R2): anchor: a request with every field is
# answered with itself; a 15-digit Nat and input left over are refused
# EXCLUDES: a vacuous wire_entry_exact (no input answered) or
#   wire_entry_refuses (no input refused)
law wire_entry_example:
  {[FW.ffi("2,7,T2,hi2,1,22,"), FW.ffi("100000000000000,1,T0,0,"), FW.ffi("1,1,T0,0,x")] == ["2,7,T2,hi2,1,22,", Wr.err("malformed wire request"), Wr.err("malformed wire request")] : List<&2, String>}
