# eukhe: lemmas of area wire_ffi
#
# The halves of a fit, the step of a spelled prefix, the spelling of a
# list as the laws spell it, and that a decoded list of Nats fits the wire
# (the chain of proof/shape/base/entry.bend, kept here so this area does
# not load the shape tables).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ../wire/base/spell.bend as LAWireSpell

# Logic
# -----

def wrb.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def wrb.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LAWireSpell.ws_absurd({b == True{} : Bool}, Equal.sym(Bool, False{}, True{}, h))

# s spelled up to a field a is s spelled up to its spelling b
def wrb.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# The spelling
# ------------

# the entry's reply spelling of n, x, b, a, xs, then rest, is the laws'
def wrb.spell(n: Nat, x: U32, b: Bool, a: String, +xs: List<&2, Nat>, +rest: String) -> {Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, Wr.put_str(a, Wr.put_list(~Nat, ~Wr.put_nat, xs, rest))))) == Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, Wr.put_str(a, LawsBase.wire_spell_nats(xs, rest))))) : String}:
  Equal.cong(String, String, z => Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, Wr.put_str(a, z)))), Wr.put_list(~Nat, ~Wr.put_nat, xs, rest), LawsBase.wire_spell_nats(xs, rest), Wire.wire_nats_spells(xs, rest))

# A decoded list of Nats fits
# ---------------------------

def wrb.GoP(m: Nat, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {List.length(&2, Nat, xs) == 1n+m : Nat} & {LawsBase.wire_nats_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def wrb.go.cons(+m: Nat, +x: Nat, fx: {LawsBase.wire_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, v: wrb.GoP(m, d)) -> wrb.GoP(1n+m, Wr.get_list.cons(Nat, x, d)):
  match d:
    case Wr.Got{+xs, r}:
      (e1, e2) = v
      (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Nat, xs), 1n+m, e1), LAWireSpell.ws_and_tt(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(xs), fx, e2))
    case Wr.Bad{}:
      Unit{}

def wrb.go(m: Nat, +s: String, cur: Wr.Dec<Nat>, ec: {Wr.get_nat(s) == cur : Wr.Dec<Nat>}) -> wrb.GoP(m, Wr.get_list.go(~Nat, ~Wr.get_nat, m, cur)):
  match m:
    case 0n:
      match cur:
        case Wr.Got{+x, +r}:
          ({==}, LAWireSpell.ws_and_tt(LawsBase.wire_fits(x), True{}, Wire.wire_nat_decoded_fits(s, x, r, ec), {==}))
        case Wr.Bad{}:
          Unit{}
    case 1n++k:
      match cur:
        case Wr.Got{+x, +r}:
          wrb.go.cons(k, x, Wire.wire_nat_decoded_fits(s, x, r, ec), Wr.get_list.go(~Nat, ~Wr.get_nat, k, Wr.get_nat(r)), wrb.go(k, r, Wr.get_nat(r), {==}))
        case Wr.Bad{}:
          Unit{}

def wrb.NF(d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def wrb.nf.go(+m: Nat, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, v: wrb.GoP(m, d)) -> wrb.NF(d):
  match d:
    case Wr.Got{+xs, r}:
      (e1, e2) = v
      %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, e1) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
      LAWireSpell.ws_and_tt(LawsBase.wire_fits(1n+m), LawsBase.wire_nats_fit(xs), fn, e2)
    case Wr.Bad{}:
      Unit{}

def wrb.nf.n(n: Nat, +s1: String, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> wrb.NF(Wr.get_list.start(~Nat, ~Wr.get_nat, Wr.Got{n, s1})):
  match n:
    case 0n:
      {==}
    case 1n++m:
      wrb.nf.go(m, fn, Wr.get_list.go(~Nat, ~Wr.get_nat, m, Wr.get_nat(s1)), wrb.go(m, s1, Wr.get_nat(s1), {==}))

def wrb.nf.start(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> wrb.NF(Wr.get_list.start(~Nat, ~Wr.get_nat, d)):
  match d:
    case Wr.Got{+n, +s1}:
      wrb.nf.n(n, s1, Wire.wire_nat_decoded_fits(s, n, s1, ed))
    case Wr.Bad{}:
      Unit{}

# a decoded list of Nats fits the wire: its count and every item
def wrb.nats_fit(+s: String, +xs: List<&2, Nat>, +r: String, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s) == Wr.Got{xs, r} : Wr.Dec<List<&2, Nat>>}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}:
  %ed : wrb.NF(_)
  wrb.nf.start(s, Wr.get_nat(s), {==})
