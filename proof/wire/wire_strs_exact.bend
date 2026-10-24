# eukhe: the proof of LAW wire_strs_exact
#
# PROOF of LAW wire_strs_exact: the pattern of wire_list_exact over
# strings. A predicate says what each decoder answer means about its
# input (an encoding, or nothing for Bad); the count is a Nat encoding
# (wire_nat_exact), each item a string encoding (wire_str_exact), so the
# input is the count, then the spelled items.

import Base
import ../../bend/wire.bend as Wr
import ../../laws/wire.bend as Wire
import ../../laws/base.bend as LawsBase
import ./wire_nat_exact.bend as PWireNatExact
import ./wire_str_exact.bend as PWireStrExact

# what the item loop's answer says about its input s (m + 1 items)
def ws_pl(s: String, m: Nat, d: Wr.Dec<List<&2, String>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == LawsBase.wire_spell_strs.items(xs, r) : String} & {List.length(&2, String, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def ws_list_step(-s: String, +x: String, +s3: String, -k: Nat, ex: {s == Wr.put_str(x, s3) : String},
  d: Wr.Dec<List<&2, String>>, ih: ws_pl(s3, k, d)) -> ws_pl(s, 1n+k, Wr.get_list.cons(String, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (Equal.trans(String, s, Wr.put_str(x, s3), Wr.put_str(x, LawsBase.wire_spell_strs.items(ys, r)), ex,
          Equal.cong(String, String, z => Wr.put_str(x, z), s3, LawsBase.wire_spell_strs.items(ys, r), e1)),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, String, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only items that are encodings
def ws_list_spec(m: Nat, cur: Wr.Dec<String>, +s: String, er: {Wr.get_str(s) == cur : Wr.Dec<String>}) ->
  ws_pl(s, m, Wr.get_list.go(~String, ~Wr.get_str, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (Wire.wire_str_exact(s, x, s3, er), {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      ws_list_step(s, x, s3, k, Wire.wire_str_exact(s, x, s3, er),
        Wr.get_list.go(~String, ~Wr.get_str, k, Wr.get_str(s3)), ws_list_spec(k, Wr.get_str(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder answer says about its input s
def ws_pls(s: String, d: Wr.Dec<List<&2, String>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == LawsBase.wire_spell_strs(xs, r) : String}
    case Wr.Bad{}:
      Unit

def ws_list_conv(+s: String, +s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  d: Wr.Dec<List<&2, String>>, pl: ws_pl(s2, m, d)) -> ws_pls(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = pl
      %Equal.sym(Nat, List.length(&2, String, xs), 1n+m, e2) : {s == Wr.put_nat(_, LawsBase.wire_spell_strs.items(xs, r)) : String}
      %e1 : {s == Wr.put_nat(1n+m, _) : String}
      en
    case Wr.Bad{}:
      Unit{}

def ws_list_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}) ->
  ws_pls(s, Wr.get_list.start(~String, ~Wr.get_str, Wr.Got{n, s2})):
  match n:
    case 0n:
      en
    case 1n++m:
      ws_list_conv(s, s2, m, en, Wr.get_list.go(~String, ~Wr.get_str, m, Wr.get_str(s2)),
        ws_list_spec(m, Wr.get_str(s2), s2, {==}))

def ws_list_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) ->
  ws_pls(s, Wr.get_list.start(~String, ~Wr.get_str, r)):
  match r:
    case Wr.Got{+n, +s2}:
      ws_list_nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, er))
    case Wr.Bad{}:
      Unit{}

def Wire.wire_strs_exact(s, xs, rest, h):
  %h : ws_pls(s, _)
  ws_list_top(s, Wr.get_nat(s), {==})
