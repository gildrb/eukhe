# eukhe: the proof of LAW wire_list_exact

import Base
import ../../bend/wire.bend as Wr
import ../../laws/wire.bend as Wire
import ../base.bend as L
import ./wire_nat_exact.bend as PWireNatExact

# what the item loop's answer says about its input s (m + 1 items)
def wr_pl(s: String, m: Nat, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == L.wr_items(xs, r) : String} & {List.length(&2, Nat, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def wr_list_step(-s: String, +x: Nat, +s3: String, -k: Nat, ex: {s == Wr.put_nat(x, s3) : String},
  d: Wr.Dec<List<&2, Nat>>, ih: wr_pl(s3, k, d)) -> wr_pl(s, 1n+k, Wr.get_list.cons(Nat, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (Equal.trans(String, s, Wr.put_nat(x, s3), Wr.put_nat(x, L.wr_items(ys, r)), ex,
          Equal.cong(String, String, z => Wr.put_nat(x, z), s3, L.wr_items(ys, r), e1)),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Nat, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only items that are encodings
def wr_list_spec(m: Nat, cur: Wr.Dec<Nat>, +s: String, er: {Wr.get_nat(s) == cur : Wr.Dec<Nat>}) ->
  wr_pl(s, m, Wr.get_list.go(~Nat, ~Wr.get_nat, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (Wire.wire_nat_exact(s, x, s3, er), {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      wr_list_step(s, x, s3, k, Wire.wire_nat_exact(s, x, s3, er),
        Wr.get_list.go(~Nat, ~Wr.get_nat, k, Wr.get_nat(s3)), wr_list_spec(k, Wr.get_nat(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder answer says about its input s
def wr_pls(s: String, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_list(~Nat, ~Wr.put_nat, xs, r) : String}
    case Wr.Bad{}:
      Unit

def wr_list_conv(+s: String, +s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  d: Wr.Dec<List<&2, Nat>>, pl: wr_pl(s2, m, d)) -> wr_pls(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = pl
      %Equal.sym(String, Wr.put_list(~Nat, ~Wr.put_nat, xs, r), Wr.put_nat(List.length(&2, Nat, xs), L.wr_items(xs, r)), L.wr_put_list(xs, r)) : {s == _ : String}
      %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, e2) : {s == Wr.put_nat(_, L.wr_items(xs, r)) : String}
      %e1 : {s == Wr.put_nat(1n+m, _) : String}
      en
    case Wr.Bad{}:
      Unit{}

def wr_list_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}) ->
  wr_pls(s, Wr.get_list.start(~Nat, ~Wr.get_nat, Wr.Got{n, s2})):
  match n:
    case 0n:
      en
    case 1n++m:
      wr_list_conv(s, s2, m, en, Wr.get_list.go(~Nat, ~Wr.get_nat, m, Wr.get_nat(s2)),
        wr_list_spec(m, Wr.get_nat(s2), s2, {==}))

def wr_list_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) ->
  wr_pls(s, Wr.get_list.start(~Nat, ~Wr.get_nat, r)):
  match r:
    case Wr.Got{+n, +s2}:
      wr_list_nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, er))
    case Wr.Bad{}:
      Unit{}

def Wire.wire_list_exact(s, xs, rest, h):
  %h : wr_pls(s, _)
  wr_list_top(s, Wr.get_nat(s), {==})
