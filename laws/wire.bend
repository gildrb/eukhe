# eukhe: the laws of area wire
#
# LAWS (the wire format of the compiled Bend core): every entry of
# bend/core.bend reads its input and writes its reply in the format of
# bend/wire.bend (grammar: crates/eukhe-bend/WIRE.md). Each law is an open
# claim about bend/wire.bend; PROOF.bend proves them (as Wire.<law>) with
# the lemmas of proof/wire/.
#
# R1: a decoder reads back what its encoder wrote, and leaves the input
#     after it untouched (so values compose: the laws quantify `rest`).
# R2: a decoder accepts only an encoder's output: any other input is
#     Bad{}, never a default (leading zeros, a missing ',', a short
#     string, a wrong count, an unknown char).
# R3: a Nat has at most 14 digits, decided while reading, so no input can
#     push a Nat past the runtime's 2^48-1 bound; a longer encoding is
#     refused, never misread.
# R4: no encoding starts with 'E', so a reply is either a value or the
#     error form 'E ' + text (the Rust Reader::reply,
#     crates/eukhe-bend/src/wire.rs, takes a reply that opens with "E " as
#     the error).
# R5: the encodings are WIRE.md's grammar: a Nat is its canonical decimal
#     digits, most significant first, each the char of code 48 + the
#     digit, then ','; a U32 is the Nat of its value; a Bool is T or F; a
#     String is its length in chars, then its chars; a List its count,
#     then its items; the error form is 'E ', then the text.

import Base
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# Terms: decimal numerals
# -----------------------
# A numeral is written as a list of digits, lowest first, so its value is
# d0 + 10 * (d1 + 10 * (d2 + ...)) with no division: the laws below state
# the spelling of a Nat by its numeral, not by the encoder's division loop.

# the value of the digits ds, lowest first
def wire_value(ds: List<&2, Nat>) -> Nat:
  match ds:
    case Nil{}:
      0n
    case Con{d, t}:
      Nat.add(d, Nat.mul(10n, wire_value(t)))

# the higher digits u (lowest first) above the digit e, then e: every
# digit below 10, and the highest one not 0
def wire_numeral.high(u: List<&2, Nat>, +e: Nat) -> Bool:
  match u:
    case Nil{}:
      Bool.and(Nat.is_lt(0n, e), Nat.is_lt(e, 10n))
    case Con{f, v}:
      Bool.and(Nat.is_lt(e, 10n), wire_numeral.high(v, f))

# the lowest digit d, then the higher digits t: a numeral
def wire_numeral.from(d: Nat, t: List<&2, Nat>) -> Bool:
  match t:
    case Nil{}:
      Nat.is_lt(d, 10n)
    case Con{e, u}:
      Bool.and(Nat.is_lt(d, 10n), wire_numeral.high(u, e))

# ds (lowest first) is a decimal numeral: at least one digit, every digit
# below 10, the highest not 0 unless it is the only one (0 is the one
# digit 0)
def wire_numeral(ds: List<&2, Nat>) -> Bool:
  match ds:
    case Nil{}:
      False{}
    case Con{d, t}:
      wire_numeral.from(d, t)

# the chars of the digits ds (lowest first) before acc: the highest digit
# comes first, each the char of code 48 + the digit
def wire_numeral_chars(ds: List<&2, Nat>, acc: String) -> String:
  match ds:
    case Nil{}:
      acc
    case Con{d, t}:
      wire_numeral_chars(t, SCon{LawsBase.wire_dec_char(d), acc})

# Nat
# ---

# LAW wire_nat_round_trip (R1): a Nat that fits reads back, and the rest is untouched
# EXCLUDES: a misread digit, digits in the wrong order, a lost or eaten rest
law wire_nat_round_trip:
  for +n: Nat
  for rest: String
  for h: {LawsBase.wire_fits(n) == True{} : Bool}
  {Wr.get_nat(Wr.put_nat(n, rest)) == Wr.Got{n, rest} : Wr.Dec<Nat>}

# LAW wire_nat_exact (R2): a decoded Nat is exactly an encoding: any other input is Bad{}
# EXCLUDES: leading zeros, a missing or another end mark, a default for
#   malformed input, a second spelling of a value
law wire_nat_exact:
  for +s: String
  for +n: Nat
  for +rest: String
  for h: {Wr.get_nat(s) == Wr.Got{n, rest} : Wr.Dec<Nat>}
  {s == Wr.put_nat(n, rest) : String}

# LAW wire_nat_decoded_fits (R3): a decoded Nat has at most 14 digits (it
# fits the wire: wire_fits, which wire_fits_digits pins to the digit count)
# EXCLUDES: a decoder that answers a value of 15 or more digits (how far
#   it folds the digits before it refuses is not seen by a law: that is
#   the run-time test crates/eukhe-bend/tests/max_magnitude.rs)
law wire_nat_decoded_fits:
  for +s: String
  for +n: Nat
  for +rest: String
  for h: {Wr.get_nat(s) == Wr.Got{n, rest} : Wr.Dec<Nat>}
  {LawsBase.wire_fits(n) == True{} : Bool}

# LAW wire_nat_too_long (R3): the encoding of a Nat too long for the wire is refused, not misread
# EXCLUDES: a truncated or wrapped value read from a long encoding
law wire_nat_too_long:
  for +n: Nat
  for rest: String
  for h: {LawsBase.wire_fits(n) == False{} : Bool}
  {Wr.get_nat(Wr.put_nat(n, rest)) == Wr.Bad{} : Wr.Dec<Nat>}

# LAW wire_too_long_exists (R3): witness: a Nat too long for the wire exists
# EXCLUDES: a vacuous wire_nat_too_long
law wire_too_long_exists:
  exs n: Nat
  {LawsBase.wire_fits(n) == False{} : Bool}

# LAW wire_nat_not_err (R4): no Nat encoding starts with 'E'
# EXCLUDES: a reply value read as the error form
law wire_nat_not_err:
  for n: Nat
  for rest: String
  {LawsBase.wire_opens_err(Wr.put_nat(n, rest)) == False{} : Bool}

# LAW wire_nat_example (R5): anchor: 42 is the digits 4 2 then ','
# EXCLUDES: a reversed, padded or unterminated spelling
law wire_nat_example:
  {Wr.put_nat(42n, "x") == "42,x" : String}

# LAW wire_nat_spells_digits (R5): every Nat n is spelled as a decimal
# numeral of value n (some digits ds, lowest first: each below 10, the
# highest not 0 unless n is 0, d0 + 10 * d1 + 100 * d2 + ... = n): its
# digits highest first, each the char of code 48 + the digit, then ','
# EXCLUDES: a writer and reader that agree on a wrong digit table (3 and
#   4 swapped both ways passes every round trip), digits in the wrong
#   order, another base, a leading zero, a missing or another end mark
law wire_nat_spells_digits:
  for +n: Nat
  for rest: String
  exs ds: List<&2, Nat>
  {(wire_numeral(ds), (wire_value(ds), Wr.put_nat(n, rest))) == (True{}, (n, wire_numeral_chars(ds, SCon{',', rest}))) : Bool & (Nat & String)}

# LAW wire_nat_zero_example (R5): anchor: 0 is one digit
# EXCLUDES: an empty spelling of 0
law wire_nat_zero_example:
  {Wr.put_nat(0n, "") == "0," : String}

# LAW wire_nat_leading_zero_example (R2): anchor: a leading zero is malformed
# EXCLUDES: a decoder that accepts 01 as 1
law wire_nat_leading_zero_example:
  {Wr.get_nat("01,") == Wr.Bad{} : Wr.Dec<Nat>}

# LAW wire_nat_unterminated_example (R2): anchor: digits with no end mark are malformed
# EXCLUDES: a decoder that accepts the end of input as the end mark
law wire_nat_unterminated_example:
  {Wr.get_nat("12") == Wr.Bad{} : Wr.Dec<Nat>}

# LAW wire_fits_digits (R3): support of the bound: wire_fits, the premise
# of every law about a Nat that fits, is "at most 14 decimal digits": a
# Nat written with the numeral ds fits exactly when ds has at most 14
# digits
# EXCLUDES: a wire_fits that counts the digits of a Nat otherwise (the
#   bound of R3, and every fits premise, would then be off)
law wire_fits_digits:
  for +ds: List<&2, Nat>
  for h: {wire_numeral(ds) == True{} : Bool}
  {LawsBase.wire_fits(wire_value(ds)) == Nat.is_le(List.length(&2, Nat, ds), 14n) : Bool}

# LAW wire_nat_overlong (R3): a run of 15 or more digit chars is never a
# Nat, whatever follows it
# EXCLUDES: a decoder that reads a digit string past the wire's 14 digits
#   and answers a value (wire_nat_too_long covers only canonical spellings
#   of a value too long for the wire; this covers every such run, a
#   leading zero or a missing end mark included)
# NOT PINNED: a law sees only the decoder's answer, not how far it folds
#   the digits before refusing; that the shipped decoder never folds past
#   14 digits (so no input stops the process at 2^48-1) is the run-time
#   boundary crates/eukhe-bend/tests/max_magnitude.rs tests
law wire_nat_overlong:
  for +ds: List<&2, Nat>
  for rest: String
  for h: {LawsBase.wire_overlong(ds) == True{} : Bool}
  {Wr.get_nat(LawsBase.wire_digit_chars(ds, rest)) == Wr.Bad{} : Wr.Dec<Nat>}

# LAW wire_nat_overlong_example (R3): anchor: 15 digits then ',' are refused
# EXCLUDES: a vacuous wire_nat_overlong
law wire_nat_overlong_example:
  {(LawsBase.wire_overlong([1n, 2n, 3n, 4n, 5n, 6n, 7n, 8n, 9n, 0n, 1n, 2n, 3n, 4n, 5n]), Wr.get_nat("123456789012345,")) == (True{}, Wr.Bad{}) : Bool & Wr.Dec<Nat>}

# LAW wire_u32_overlong (R3): a run of 15 or more digit chars is never a
# U32, whatever follows it
# EXCLUDES: a U32 reader with its own digit loop that folds a long run
#   before its range check (the U32 laws above see only canonical
#   spellings)
law wire_u32_overlong:
  for +ds: List<&2, Nat>
  for rest: String
  for h: {LawsBase.wire_overlong(ds) == True{} : Bool}
  {Wr.get_u32(LawsBase.wire_digit_chars(ds, rest)) == Wr.Bad{} : Wr.Dec<U32>}

# U32
# ---

# LAW wire_u32_round_trip (R1): every U32 reads back, and the rest is untouched
# EXCLUDES: a U32 that wraps, loses high bits or eats the rest
law wire_u32_round_trip:
  for +x: U32
  for rest: String
  {Wr.get_u32(Wr.put_u32(x, rest)) == Wr.Got{x, rest} : Wr.Dec<U32>}

# LAW wire_u32_exact (R2): a decoded U32 is exactly an encoding: any other input is Bad{}
# EXCLUDES: a Nat above 4294967295 read (wrapped) as a U32, a default for
#   malformed input
law wire_u32_exact:
  for +s: String
  for +x: U32
  for +rest: String
  for h: {Wr.get_u32(s) == Wr.Got{x, rest} : Wr.Dec<U32>}
  {s == Wr.put_u32(x, rest) : String}

# LAW wire_u32_example (R5): anchor: a small U32 is its decimal
# EXCLUDES: a U32 spelled in another base or width
law wire_u32_example:
  {Wr.put_u32(7, "") == "7," : String}

# LAW wire_u32_reads_decimal (R1, R5): the U32 reader reads the decimal spelling (wire_dec) of every U32
# EXCLUDES: a U32 reader that reads only its own writer's (wrong) digits
law wire_u32_reads_decimal:
  for +x: U32
  for rest: String
  {Wr.get_u32(LawsBase.wire_dec(U32.to_nat(x), rest)) == Wr.Got{x, rest} : Wr.Dec<U32>}

# Bool
# ----

# LAW wire_bool_round_trip (R1): every Bool reads back, and the rest is untouched
# EXCLUDES: a swapped or constant Bool
law wire_bool_round_trip:
  for b: Bool
  for rest: String
  {Wr.get_bool(Wr.put_bool(b, rest)) == Wr.Got{b, rest} : Wr.Dec<Bool>}

# LAW wire_bool_exact (R2): a decoded Bool is exactly an encoding: any other input is Bad{}
# EXCLUDES: any char other than T and F read as a Bool
law wire_bool_exact:
  for +s: String
  for +b: Bool
  for +rest: String
  for h: {Wr.get_bool(s) == Wr.Got{b, rest} : Wr.Dec<Bool>}
  {s == Wr.put_bool(b, rest) : String}

# LAW wire_bool_not_err (R4): no Bool encoding starts with 'E'
# EXCLUDES: a reply value read as the error form
law wire_bool_not_err:
  for b: Bool
  for rest: String
  {LawsBase.wire_opens_err(Wr.put_bool(b, rest)) == False{} : Bool}

# LAW wire_bool_example (R5): anchor: True is T
# EXCLUDES: another spelling of True
law wire_bool_example:
  {Wr.put_bool(True{}, "F") == "TF" : String}

# LAW wire_bool_false_example (R5): anchor: False is F
# EXCLUDES: another spelling of False (the two rows of WIRE.md's T | F)
law wire_bool_false_example:
  {Wr.put_bool(False{}, "") == "F" : String}

# String
# ------

# LAW wire_str_round_trip (R1): a string whose length fits reads back, and the rest is untouched
# EXCLUDES: a length counted in another unit, a lost, added or changed char
law wire_str_round_trip:
  for +a: String
  for rest: String
  for h: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
  {Wr.get_str(Wr.put_str(a, rest)) == Wr.Got{a, rest} : Wr.Dec<String>}

# LAW wire_str_exact (R2): a decoded string is exactly an encoding: any other input is Bad{}
# EXCLUDES: a short string padded or accepted, a wrong length, a default
law wire_str_exact:
  for +s: String
  for +a: String
  for +rest: String
  for h: {Wr.get_str(s) == Wr.Got{a, rest} : Wr.Dec<String>}
  {s == Wr.put_str(a, rest) : String}

# LAW wire_str_example (R5): anchor: the length counts chars, not bytes
# EXCLUDES: a length in UTF-8 bytes
law wire_str_example:
  {Wr.put_str("hé", "!") == "2,hé!" : String}

# LAW wire_str_decimal (R5): a string is its length in chars in decimal (wire_dec), then its chars
# EXCLUDES: a length writer and reader that agree on a wrong digit table,
#   order or base (the example's length has one digit)
law wire_str_decimal:
  for +a: String
  for rest: String
  {Wr.put_str(a, rest) == LawsBase.wire_dec_str(a, rest) : String}

# LAW wire_str_reads_decimal (R1, R5): the string reader reads the decimal spelling of a string whose length fits
# EXCLUDES: a reader that reads only its own writer's length digits
law wire_str_reads_decimal:
  for +a: String
  for rest: String
  for h: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
  {Wr.get_str(LawsBase.wire_dec_str(a, rest)) == Wr.Got{a, rest} : Wr.Dec<String>}

# Lists
# -----

# LAW wire_list_round_trip (R1): a list of Nats that fit, of a length that fits, reads back
# EXCLUDES: lost, added, reordered or misread items, a wrong count
law wire_list_round_trip:
  for +xs: List<&2, Nat>
  for rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
  {Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Nat>>}

# LAW wire_list_exact (R2): a decoded list is exactly an encoding: any other input is Bad{}
# EXCLUDES: a count larger than the items accepted, a default
law wire_list_exact:
  for +s: String
  for +xs: List<&2, Nat>
  for +rest: String
  for h: {Wr.get_list(~Nat, ~Wr.get_nat, s) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Nat>>}
  {s == Wr.put_list(~Nat, ~Wr.put_nat, xs, rest) : String}

# LAW wire_list_example (R5): anchor: a list is its count, then its items
# EXCLUDES: items with no count, a count after the items
law wire_list_example:
  {Wr.put_list(~Nat, ~Wr.put_nat, [1n, 22n], "") == "2,1,22," : String}

# LAW wire_nats_decimal (R5): a list of Nats is its count in decimal, then each Nat in decimal
# EXCLUDES: a list count (or item) writer and reader that agree on a wrong
#   digit table, order or base
law wire_nats_decimal:
  for +xs: List<&2, Nat>
  for rest: String
  {Wr.put_list(~Nat, ~Wr.put_nat, xs, rest) == LawsBase.wire_dec_nats(xs, rest) : String}

# LAW wire_nats_reads_decimal (R1, R5): the list reader reads the decimal spelling of a list of Nats that fits
# EXCLUDES: a list reader that reads only its own writer's count digits
law wire_nats_reads_decimal:
  for +xs: List<&2, Nat>
  for rest: String
  for h: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
  {Wr.get_list(~Nat, ~Wr.get_nat, LawsBase.wire_dec_nats(xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Nat>>}

# Replies
# -------

# LAW wire_err_example (R4, R5): anchor: WIRE.md's error reply: 'E ', then the text
# EXCLUDES: another error spelling the Rust Reader would read as a value
law wire_err_example:
  {Wr.err("bad input") == "E bad input" : String}

# LAW wire_err_never_value (R4): an error reply is never read as a value:
# for every text, the Nat, Bool and String readers refuse the error form
# (so do the U32 and list readers, which start with the Nat reader)
# EXCLUDES: an error reply read as a count, a flag or a text (a reader that
#   skips a leading 'E', or an error form that opens with a digit, T or F)
law wire_err_never_value:
  for +text: String
  {(Wr.get_nat(Wr.err(text)), (Wr.get_bool(Wr.err(text)), Wr.get_str(Wr.err(text)))) == (Wr.Bad{}, (Wr.Bad{}, Wr.Bad{})) : Wr.Dec<Nat> & (Wr.Dec<Bool> & Wr.Dec<String>)}

# Lists of strings, and the spec spellers
# ---------------------------------------

# LAW wire_strs_spells (R5): a list of strings is spelled LawsBase.wire_spell_strs: its count, then each string
# EXCLUDES: items in another order, a count after the items, a separator
law wire_strs_spells:
  for +xs: List<&2, String>
  for rest: String
  {Wr.put_list(~String, ~Wr.put_str, xs, rest) == LawsBase.wire_spell_strs(xs, rest) : String}

# LAW wire_nats_spells (R5): a list of Nats is spelled LawsBase.wire_spell_nats: its count, then each Nat
# EXCLUDES: items in another order, a count after the items, a separator
law wire_nats_spells:
  for +xs: List<&2, Nat>
  for rest: String
  {Wr.put_list(~Nat, ~Wr.put_nat, xs, rest) == LawsBase.wire_spell_nats(xs, rest) : String}

# LAW wire_strs_round_trip (R1): a list of strings that fits reads back, and the rest is untouched
# EXCLUDES: a lost, added, reordered or changed string, a wrong count
law wire_strs_round_trip:
  for +xs: List<&2, String>
  for rest: String
  for h: {LawsBase.wire_strs_fit(xs) == True{} : Bool}
  {Wr.get_list(~String, ~Wr.get_str, LawsBase.wire_spell_strs(xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, String>>}

# LAW wire_strs_exact (R2): a decoded list of strings is exactly its spelling: any other input is Bad{}
# EXCLUDES: a count larger than the strings accepted, a short string
#   padded, a default
law wire_strs_exact:
  for +s: String
  for +xs: List<&2, String>
  for +rest: String
  for h: {Wr.get_list(~String, ~Wr.get_str, s) == Wr.Got{xs, rest} : Wr.Dec<List<&2, String>>}
  {s == LawsBase.wire_spell_strs(xs, rest) : String}

# LAW wire_str_decoded_fits (R3): a decoded string fits the wire: its length has at most 14 digits
# EXCLUDES: a string read with a length the wire cannot carry
law wire_str_decoded_fits:
  for +s: String
  for +a: String
  for +rest: String
  for h: {Wr.get_str(s) == Wr.Got{a, rest} : Wr.Dec<String>}
  {LawsBase.wire_fits(String.length(a)) == True{} : Bool}

# LAW wire_strs_decoded_fit (R3): a decoded list of strings fits the wire: its count and every string
# EXCLUDES: a list read with a count or a string the wire cannot carry
law wire_strs_decoded_fit:
  for +s: String
  for +xs: List<&2, String>
  for +rest: String
  for h: {Wr.get_list(~String, ~Wr.get_str, s) == Wr.Got{xs, rest} : Wr.Dec<List<&2, String>>}
  {LawsBase.wire_strs_fit(xs) == True{} : Bool}

# LAW wire_strs_example (R5): anchor: a list of strings is its count, then each string (its length, then its chars)
# EXCLUDES: strings with no length, a count of chars instead of strings
law wire_strs_example:
  {Wr.put_list(~String, ~Wr.put_str, ["ab", "c"], "") == "2,2,ab1,c" : String}

# LAW wire_strs_decimal (R5): a list of strings is its count in decimal, then each string (wire_dec_str)
# EXCLUDES: a count or length writer and reader that agree on a wrong
#   digit table, order or base
law wire_strs_decimal:
  for +xs: List<&2, String>
  for rest: String
  {Wr.put_list(~String, ~Wr.put_str, xs, rest) == LawsBase.wire_dec_strs(xs, rest) : String}

# LAW wire_strs_reads_decimal (R1, R5): the list reader reads the decimal spelling of a list of strings that fits
# EXCLUDES: a reader that reads only its own writer's count or length digits
law wire_strs_reads_decimal:
  for +xs: List<&2, String>
  for rest: String
  for h: {LawsBase.wire_strs_fit(xs) == True{} : Bool}
  {Wr.get_list(~String, ~Wr.get_str, LawsBase.wire_dec_strs(xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, String>>}

# Lists of any item
# -----------------
# The list codec is a template over the item's codec; the laws above pin it
# at Nat and String items. These pin it at every item codec, so a spec
# reader or writer built on Wr.get_list or Wr.put_list (a list of calls, of
# rows, of records) moves with no bug of the list codec.

# LAW wire_list_reads_items (R1, R2): for every item reader, the list
# reader reads the count, then exactly that many items one after another,
# then answers the rest; a list with fewer items than its count, or an
# item the item reader refuses, is Bad{}
# EXCLUDES: a list reader that stops early at a list cut short, pads it,
#   reads more or fewer items than the count, or behaves by the item
#   reader (a mode for item readers that swallow their input: the Nat and
#   String list laws then hold while a list of calls cut short is read)
law wire_list_reads_items:
  for ~A: Data
  for ~get: String -> Wr.Dec<A>
  for +s: String
  {Wr.get_list(~A, ~get, s) == LawsBase.wire_read_list(~A, ~get, s) : Wr.Dec<List<&2, A>>}

# LAW wire_list_spells_items (R5): for every item writer, a list is its
# count in decimal (wire_dec), then each item by the item writer, in
# order, then rest
# EXCLUDES: a list writer that drops, repeats or reorders items, or counts
#   or spells the count otherwise, for some item writer
law wire_list_spells_items:
  for ~A: Data
  for ~put: A -> String -> String
  for +xs: List<&2, A>
  for rest: String
  {Wr.put_list(~A, ~put, xs, rest) == LawsBase.wire_dec(List.length(&2, A, xs), LawsBase.wire_put_items(~A, ~put, xs, rest)) : String}

# LAW wire_list_short_example (R2): anchor: a list of lists of strings
# whose count says 2 but that holds one is Bad
# EXCLUDES: a list cut short read as a shorter list
law wire_list_short_example:
  {Wr.get_list(~List<&2, String>, ~(s => Wr.get_list(~String, ~Wr.get_str, s)), "2,1,1,a") == Wr.Bad{} : Wr.Dec<List<&2, List<&2, String>>>}

# LAW wire_err_example (R4): the error form is 'E ', then the text
# EXCLUDES: another error spelling the Rust Reader would read as a value
law wire_err_example_orig:
  for text: String
  {Wr.err(text) == SCon{'E', SCon{' ', text}} : String}
