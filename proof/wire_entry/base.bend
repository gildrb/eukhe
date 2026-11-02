# eukhe: lemmas shared by the proofs of area wire_entry: the halves of an
# and, and a decoded list of Nats fits the wire (its count and every item),
# read off the spec's list reader (wire_list_reads_items)

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_list_reads_items.bend as PWireListReadsItems
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits

# Bool
# ----

def web.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True
def web.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : web.If(_, G)
  Unit{}

def web.and_l(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      e

def web.and_r(+a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      web.absurd({b == True{} : Bool}, e)

def web.and_tt(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, hb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

# A decoded list of Nats fits
# ---------------------------

# what the spec's item loop answers for n items: n items, each fitting
def web.ItP(n: Nat, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {List.length(&2, Nat, xs) == n : Nat} & {LawsBase.wire_nats_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# an item that fits in front of m items that fit
def web.cons(+x: Nat, -m: Nat, fx: {LawsBase.wire_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ih: web.ItP(m, d)) ->
  web.ItP(1n+m, LawsBase.wire_items.cons(Nat, x, d)):
  match d:
    case Wr.Got{+xs, r}:
      (el, ef) = ih
      (Equal.cong(Nat, Nat, k => 1n+k, List.length(&2, Nat, xs), m, el), web.and_tt(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(xs), fx, ef))
    case Wr.Bad{}:
      Unit{}

# the first of m + 1 items, read by the Nat reader at s, then m more
def web.then(+m: Nat, +s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>},
  ih: @r: String -> web.ItP(m, LawsBase.wire_items(~Nat, ~Wr.get_nat, m, r))) ->
  web.ItP(1n+m, LawsBase.wire_items.then(Nat, d, r => LawsBase.wire_items(~Nat, ~Wr.get_nat, m, r))):
  match d:
    case Wr.Got{+x, +r}:
      web.cons(x, m, Wire.wire_nat_decoded_fits(s, x, r, ed), LawsBase.wire_items(~Nat, ~Wr.get_nat, m, r), ih(r))
    case Wr.Bad{}:
      Unit{}

# the spec's item loop reads n items, each fitting
def web.items(n: Nat, +s: String) -> web.ItP(n, LawsBase.wire_items(~Nat, ~Wr.get_nat, n, s)):
  match n:
    case 0n:
      ({==}, {==})
    case 1n++m:
      web.then(m, s, Wr.get_nat(s), {==}, r => web.items(m, r))

# what a list reader's answer says: the list fits
def web.LP(d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def web.count_fits(-n: Nat, hn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ip: web.ItP(n, d)) -> web.LP(d):
  match d:
    case Wr.Got{+xs, r}:
      (el, ef) = ip
      %Equal.sym(Nat, List.length(&2, Nat, xs), n, el) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
      web.and_tt(LawsBase.wire_fits(n), LawsBase.wire_nats_fit(xs), hn, ef)
    case Wr.Bad{}:
      Unit{}

def web.count(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) ->
  web.LP(LawsBase.wire_read_list.count(~Nat, ~Wr.get_nat, d)):
  match d:
    case Wr.Got{+n, +r}:
      web.count_fits(n, Wire.wire_nat_decoded_fits(s, n, r, ed), LawsBase.wire_items(~Nat, ~Wr.get_nat, n, r), web.items(n, r))
    case Wr.Bad{}:
      Unit{}

# a list of Nats the list reader decodes fits the wire: its count and every
# item (the reader is the spec's: wire_list_reads_items)
def web.list_fits(+s: String, +xs: List<&2, Nat>, +rest: String,
  h: {Wr.get_list(~Nat, ~Wr.get_nat, s) == Wr.Got{xs, rest} : Wr.Dec<List<&2, Nat>>}) ->
  {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}:
  +e = Equal.trans(Wr.Dec<List<&2, Nat>>, LawsBase.wire_read_list(~Nat, ~Wr.get_nat, s), Wr.get_list(~Nat, ~Wr.get_nat, s), Wr.Got{xs, rest},
    Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, s), LawsBase.wire_read_list(~Nat, ~Wr.get_nat, s), Wire.wire_list_reads_items(~Nat, ~Wr.get_nat, s)), h)
  %e : web.LP(_)
  web.count(s, Wr.get_nat(s), {==})
