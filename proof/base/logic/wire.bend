# eukhe: lemmas the proofs of two or more areas share: logic/wire

import Base
import ../../../bend/wire.bend as Wr
import ../../../bend/wire_flat.bend as Fl
import ./nat.bend as LLogicNat

# The proofs of LAWS.bend section wire (bend/wire.bend): the Nat codec
# (lemmas wn_), the U32 codec (wu_), and the Bool, String and List codecs
# and the replies (wr_). The kit lemmas are copied from the bend skill's
# examples/sort/proof (kit.bend, nat_add.bend, u32_order.bend).

# ---- wire: nat ----

# ---- wire nat (wo_): the list decoder, the reference the fast one equals ----

# bend/wire.bend reads a Nat in one flat loop that folds the value as it
# reads. The proofs below are about this reference: it collects the digits
# (read last first) and folds them at the end. wn_eqv proves the two equal
# on every input, so every lemma about the reference holds for get_nat.

# The token at the head of s and the rest (the end of input reads Other).
def wo_peek(s: String) -> Wr.Tok & String:
  match s:
    case SNil{}:
      (Wr.Other{}, SNil{})
    case SCon{c, t}:
      (Wr.tok(c), t)

# No digit is left: only the end mark may follow.
def wo_end(ts: Wr.Tok & String, ds: List<&2, Nat>) -> Wr.Dec<Nat>:
  (t, s) = ts
  match t:
    case Wr.Dig{d}:
      Wr.Bad{}
    case Wr.Comma{}:
      Wr.Got{LLogicNat.wo_value(ds), s}
    case Wr.Other{}:
      Wr.Bad{}

# Read at most k more digits after ds (read last first), then ','.
def wo_go(k: Nat, ts: Wr.Tok & String, ds: List<&2, Nat>) -> Wr.Dec<Nat>:
  match k:
    case 0n:
      wo_end(ts, ds)
    case 1n+j:
      (t, s) = ts
      match t:
        case Wr.Dig{d}:
          wo_go(j, wo_peek(s), d <> ds)
        case Wr.Comma{}:
          Wr.Got{LLogicNat.wo_value(ds), s}
        case Wr.Other{}:
          Wr.Bad{}

def wo_lead(d: Nat, ts: Wr.Tok & String) -> Wr.Dec<Nat>:
  match d:
    case 0n:
      wo_end(ts, [0n])
    case 1n+p:
      wo_go(13n, ts, [1n+p])

# The first digit: 0 stands alone, any other starts up to 13 more.
def wo_first(ts: Wr.Tok & String) -> Wr.Dec<Nat>:
  (t, s) = ts
  match t:
    case Wr.Dig{d}:
      wo_lead(d, wo_peek(s))
    case Wr.Comma{}:
      Wr.Bad{}
    case Wr.Other{}:
      Wr.Bad{}

def wo_get_nat(s: String) -> Wr.Dec<Nat>:
  wo_first(wo_peek(s))

# the reference take: the chars one by one, head first
def wo_take_cons(c: Char, r: Wr.Dec<String>) -> Wr.Dec<String>:
  match r:
    case Wr.Got{a, s}:
      Wr.Got{SCon{c, a}, s}
    case Wr.Bad{}:
      Wr.Bad{}

# The first n chars of s and the rest.
def wo_take(n: Nat, s: String) -> Wr.Dec<String>:
  match n:
    case 0n:
      Wr.Got{SNil{}, s}
    case 1n+m:
      match s:
        case SNil{}:
          Wr.Bad{}
        case SCon{c, t}:
          wo_take_cons(c, wo_take(m, t))

# the chars of an answer of the reference, after acc turned around
def wr_tfix(acc: String, r: Wr.Dec<String>) -> Wr.Dec<String>:
  match r:
    case Wr.Got{a, s}:
      Wr.Got{String.reverse.go(acc, a), s}
    case Wr.Bad{}:
      Wr.Bad{}

def wr_tfix_cons(-acc: String, -c: Char, r: Wr.Dec<String>) ->
  {wr_tfix(SCon{c, acc}, r) == wr_tfix(acc, wo_take_cons(c, r)) : Wr.Dec<String>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

def wr_tfix_nil(r: Wr.Dec<String>) -> {wr_tfix(SNil{}, r) == r : Wr.Dec<String>}:
  match r:
    case Wr.Got{a, s}:
      {==}
    case Wr.Bad{}:
      {==}

# ---- ffi_edges ----

# The proofs of the compiled-core entry laws of the W9 areas (LAWS.bend:
# tools_ffi_*, tiny_ffi_*, catalog_union_ffi_*, gateway_width_ffi_*,
# path_policy_ffi_*). A request is a record of the wire's Nat lists (and a
# Bool), so each round trip is the wire's list round trip (Laws.
# wire_list_round_trip) and a lemma that the request's parts decode from
# their lists (`fe.*`). An entry answers a request read whole with the
# model's reply, and anything else with the error form.

# Lists of lists (bend/wire_flat.bend)
# ------------------------------------

def fe.lists_of(t: List<&2, List<&2, Nat>>) -> Fl.St:
  match t:
    case Nil{}:
      Fl.Start{}
    case xs <> d:
      Fl.Mid{xs, d}
