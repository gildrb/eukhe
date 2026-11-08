# eukhe: lemmas of LAW tools_ffi_reads_only_requests, shared by the
# spelled entry laws of tools, tiny, catalog_union and gateway_width (each
# request is wire lists of Nats): what the list decoder reads is the
# spelling of a list that fits (its count and every item), then its rest.
#
#   nl.nl(s) : nl.NL(s, Wr.get_list(~Nat, ~Wr.get_nat, s))

import Base
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/base/spell.bend as LAWireSpell
import ../../wire/wire_list_exact.bend as PWireListExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_nats_spells.bend as PWireNatsSpells

# the item loop (m + 1 items): its items fit, and there are m + 1
def nl.LF(d: Wr.Dec<List<&2, Nat>>, m: Nat) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {LawsBase.wire_nats_fit(xs) == True{} : Bool} & {List.length(&2, Nat, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def nl.lf_step(+x: Nat, fx: {LawsBase.wire_fits(x) == True{} : Bool}, -k: Nat, d: Wr.Dec<List<&2, Nat>>, ih: nl.LF(d, k)) -> nl.LF(Wr.get_list.cons(Nat, x, d), 1n+k):
  match d:
    case Wr.Got{+ys, r}:
      (f, n) = ih
      (LAWireSpell.ws_and_tt(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(ys), fx, f), Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Nat, ys), 1n+k, n))
    case Wr.Bad{}:
      Unit{}

def nl.lf_go(m: Nat, cur: Wr.Dec<Nat>, +s: String, er: {Wr.get_nat(s) == cur : Wr.Dec<Nat>}) -> nl.LF(Wr.get_list.go(~Nat, ~Wr.get_nat, m, cur), m):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (LAWireSpell.ws_and_tt(LawsBase.wire_fits(x), True{}, Wire.wire_nat_decoded_fits(s, x, s3, er), {==}), {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      nl.lf_step(x, Wire.wire_nat_decoded_fits(s, x, s3, er), k, Wr.get_list.go(~Nat, ~Wr.get_nat, k, Wr.get_nat(s3)), nl.lf_go(k, Wr.get_nat(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

# a list read fits: its count and every item
def nl.F(d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def nl.f_go(-m: Nat, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, lf: nl.LF(d, m)) -> nl.F(d):
  match d:
    case Wr.Got{+xs, r}:
      (f, n) = lf
      %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, n) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
      LAWireSpell.ws_and_tt(LawsBase.wire_fits(1n+m), LawsBase.wire_nats_fit(xs), fn, f)
    case Wr.Bad{}:
      Unit{}

def nl.f_start(n: Nat, +s2: String, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> nl.F(Wr.get_list.start(~Nat, ~Wr.get_nat, Wr.Got{n, s2})):
  match n:
    case 0n:
      LAWireSpell.ws_and_tt(LawsBase.wire_fits(0n), True{}, fn, {==})
    case 1n++m:
      nl.f_go(m, fn, Wr.get_list.go(~Nat, ~Wr.get_nat, m, Wr.get_nat(s2)), nl.lf_go(m, Wr.get_nat(s2), s2, {==}))

def nl.f_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> nl.F(Wr.get_list.start(~Nat, ~Wr.get_nat, r)):
  match r:
    case Wr.Got{+n, +s2}:
      nl.f_start(n, s2, Wire.wire_nat_decoded_fits(s, n, s2, er))
    case Wr.Bad{}:
      Unit{}

# what the list decoder reads is the spelling of a list that fits, then
# its rest
def nl.NL(s: String, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LawsBase.wire_spell_nats(xs, r) : String} & {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def nl.at(+s: String, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s) == d : Wr.Dec<List<&2, Nat>>}, fd: nl.F(d)) -> nl.NL(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (Equal.trans(String, s, Wr.put_list(~Nat, ~Wr.put_nat, xs, r), LawsBase.wire_spell_nats(xs, r), Wire.wire_list_exact(s, xs, r, ed), Wire.wire_nats_spells(xs, r)), fd)
    case Wr.Bad{}:
      Unit{}

def nl.nl(+s: String) -> nl.NL(s, Wr.get_list(~Nat, ~Wr.get_nat, s)):
  nl.at(s, Wr.get_list(~Nat, ~Wr.get_nat, s), {==}, nl.f_top(s, Wr.get_nat(s), {==}))

# s spelled up to a field a is s spelled up to its spelling b
def nl.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))
