# eukhe: the spec helpers the laws of two or more areas use

import Base
import ../bend/semver.bend as Sv

# x is written with at most 14 digits
def rank_spec.short(+x: Nat) -> Bool:
  Nat.is_le(List.length(&2, Sv.Dig, Sv.Num.dec(x)), 14n)

# ---- wire ----

# LAWS (the wire format of the compiled Bend core): every entry of
# bend/core.bend reads its input and writes its reply in the format of
# bend/wire.bend (grammar: crates/eukhe-bend/WIRE.md). Each law is an open
# claim about bend/wire.bend; PROOF.bend proves them (as Laws.<law>) with
# the lemmas of PROOF.bend section wire.
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
#     error form 'E ' + text.

# Spec helpers
# ------------

# 1 + how many more decimal digits follow the lowest one of a value whose
# higher part is q (the fuel f >= q is enough)
def wire_digits.go(f: Nat, q: Nat) -> Nat:
  match f:
    case 0n:
      0n
    case 1n+g:
      match q:
        case 0n:
          0n
        case 1n+p:
          +m = {1n+p : Nat}
          1n+wire_digits.go(g, Nat.div(m, 10n))

# how many decimal digits n has (0 has one)
def wire_digits(n: Nat) -> Nat:
  +m = n
  1n+wire_digits.go(m, Nat.div(m, 10n))

# n fits the wire: at most 14 decimal digits
def wire_fits(n: Nat) -> Bool:
  Nat.is_le(wire_digits(n), 14n)

# every item of xs fits the wire
def wire_nats_fit(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case Con{+x, t}:
      Bool.and(wire_fits(x), wire_nats_fit(t))

# s starts with the char 'E' (the error form of a reply)
def wire_opens_err(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Char.is_eq(c, 'E')

# ---- core entries ----

# LAWS: the entries of the compiled Bend core (bend/core.bend) for the
# thinking ladder, the strict plan and the thinking budgets
# (bend/ffi_effort.bend, bend/ffi_infer.bend, bend/ffi_facts.bend). Each law
# is an open claim about those files; PROOF.bend proves them (as
# Laws.<law>) on the lemmas of PROOF.bend section wire.
#
# R1: a request Rust writes (`put_req`, the grammar of the file's header,
#     every Nat and list length within the wire) reads back whole: no field
#     lost, invented, swapped or reordered, and the rest untouched.
# R2: the entry answers that request with the encoding of the model's
#     decision: the Rust rule is the proven model.
# R3: a malformed request, or one with input left over, answers the
#     entry's error form, never a default decision.
# Every input is free: any facts, maps, levels, tools, caps, budgets and
# any text.

# what fits the wire: a Maybe<Nat> whose Nat fits (None always does)
def core_mfits(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      wire_fits(x)

# a content id or a token that fits the wire (None always does)
def wire_mfits(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      wire_fits(x)
