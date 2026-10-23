# eukhe: the laws of area wire

import Base
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

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

# LAW wire_nat_decoded_fits (R3): a decoded Nat fits: the decoder never reads a 15th digit
# EXCLUDES: a decoder that folds an unbounded digit string (and stops the
#   process past 2^48-1)
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

# LAW wire_nat_example (R1): anchor: 42 is the digits 4 2 then ','
# EXCLUDES: a reversed, padded or unterminated spelling
law wire_nat_example:
  {Wr.put_nat(42n, "x") == "42,x" : String}

# LAW wire_nat_zero_example (R1): anchor: 0 is one digit
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

# LAW wire_digits_spells (R3): the encoding of n spells wire_digits(n) digits, then ','
# EXCLUDES: a wire_digits that counts other than the digits the encoder
#   writes (the bound of R3 would then be off)
law wire_digits_spells:
  for +n: Nat
  {String.length(Wr.put_nat(n, "")) == 1n+LawsBase.wire_digits(n) : Nat}

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

# LAW wire_u32_example (R1): anchor: a small U32 is its decimal
# EXCLUDES: a U32 spelled in another base or width
law wire_u32_example:
  {Wr.put_u32(7, "") == "7," : String}

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

# LAW wire_bool_example (R1): anchor: True is T
# EXCLUDES: another spelling of True
law wire_bool_example:
  {Wr.put_bool(True{}, "F") == "TF" : String}

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

# LAW wire_str_example (R1): anchor: the length counts chars, not bytes
# EXCLUDES: a length in UTF-8 bytes
law wire_str_example:
  {Wr.put_str("hé", "!") == "2,hé!" : String}

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

# LAW wire_list_example (R1): anchor: a list is its count, then its items
# EXCLUDES: items with no count, a count after the items
law wire_list_example:
  {Wr.put_list(~Nat, ~Wr.put_nat, [1n, 22n], "") == "2,1,22," : String}

# Replies
# -------

# LAW wire_err_example (R4): the error form is 'E ', then the text
# EXCLUDES: another error spelling the Rust Reader would read as a value
law wire_err_example:
  for text: String
  {Wr.err(text) == SCon{'E', SCon{' ', text}} : String}

# LAW wire_end_exact (R2): the end check is exactly "nothing is left"
# EXCLUDES: an entry that ignores input left over, or refuses a fully read
#   request
law wire_end_exact:
  for +s: String
  {Wr.end(s) == String.is_empty(s) : Bool}
