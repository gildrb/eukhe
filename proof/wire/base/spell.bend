# eukhe: the proof kit of the spec spellers of laws/base.bend: lemmas an
# area's entry proofs call when its laws spell requests and replies with
# LawsBase.wire_spell_strs / LawsBase.wire_spell_nats and the W primitives. The
# laws themselves are the main kit (fills in proof/wire/<law>.bend):
#   Wire.wire_strs_spells(xs, rest)   put_list of strings == wire_spell_strs
#   Wire.wire_nats_spells(xs, rest)   put_list of Nats == wire_spell_nats
#   Wire.wire_strs_round_trip(xs, rest, h)          read back (fits)
#   Wire.wire_strs_exact(s, xs, rest, h)            decoded => spelled
#   Wire.wire_strs_decoded_fit(s, xs, rest, h)      decoded => fits
#   Wire.wire_str_decoded_fits(s, a, rest, h)       decoded string fits
# with Wire.wire_{nat,u32,bool,str}_{round_trip,exact} and
# Wire.wire_nat_decoded_fits for the primitives. Here: ws_and_tt (an and
# of two facts), ws_err_opens / ws_absurd (an error reply contradicts a
# premise that the answer is not the error form), ws_nat_read (an encoded
# Nat reads back, or Bad when too long: for tags past the last one).

import Base
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../base/wire.bend as LWire
import ../wire_nat_too_long.bend as PWireNatTooLong

# ---- Bool ----

# both halves of an and hold
def ws_and_tt(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# ---- the error form ----

# an error reply opens with 'E': it is never a value (wire_nat_not_err,
# wire_bool_not_err)
def ws_err_opens(text: String) -> {LawsBase.wire_opens_err(Wr.err(text)) == True{} : Bool}:
  {==}

# the goal G when b is False (nothing when True)
def ws_if(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

# False is not True: an answer that opens with 'E' contradicts a premise
# that it does not
def ws_absurd(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : ws_if(_, G)
  Unit{}

# ---- Nat ----

# what an encoded Nat reads as: itself when it fits (b), else Bad
def ws_nat_answer(b: Bool, n: Nat, rest: String) -> Wr.Dec<Nat>:
  match b:
    case True{}:
      Wr.Got{n, rest}
    case False{}:
      Wr.Bad{}

def ws_nat_read.at(b: Bool, +n: Nat, +rest: String, e: {LawsBase.wire_fits(n) == b : Bool}) -> {Wr.get_nat(Wr.put_nat(n, rest)) == ws_nat_answer(b, n, rest) : Wr.Dec<Nat>}:
  match b:
    case True{}:
      Wire.wire_nat_round_trip(n, rest, e)
    case False{}:
      Wire.wire_nat_too_long(n, rest, e)

# every encoded Nat reads back, or reads Bad when too long: rewrite with
# it, then split on ws_nat_answer's Bool (a tag past the last one is Bad
# both ways)
def ws_nat_read(+n: Nat, +rest: String) -> {Wr.get_nat(Wr.put_nat(n, rest)) == ws_nat_answer(LawsBase.wire_fits(n), n, rest) : Wr.Dec<Nat>}:
  ws_nat_read.at(LawsBase.wire_fits(n), n, rest, {==})
