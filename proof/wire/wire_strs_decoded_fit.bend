# eukhe: the proof of LAW wire_strs_decoded_fit
#
# PROOF of LAW wire_strs_decoded_fit: every decoded string fits
# (wire_str_decoded_fits), the loop reads exactly the count's items, and
# the count is a decoded Nat, so it fits (wire_nat_decoded_fits).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ./base/spell.bend as LAWireSpell
import ./wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ./wire_str_decoded_fits.bend as PWireStrDecodedFits

# what the item loop's answer says (m + 1 items): every string fits
def ws_fl(m: Nat, d: Wr.Dec<List<&2, String>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {LawsBase.wire_strs_all(xs) == True{} : Bool} & {List.length(&2, String, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def ws_fl_step(+x: String, -k: Nat, hx: {LawsBase.wire_fits(String.length(x)) == True{} : Bool},
  d: Wr.Dec<List<&2, String>>, ih: ws_fl(k, d)) -> ws_fl(1n+k, Wr.get_list.cons(String, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (LAWireSpell.ws_and_tt(LawsBase.wire_fits(String.length(x)), LawsBase.wire_strs_all(ys), hx, e1),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, String, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

def ws_fl_spec(m: Nat, cur: Wr.Dec<String>, +s: String, er: {Wr.get_str(s) == cur : Wr.Dec<String>}) ->
  ws_fl(m, Wr.get_list.go(~String, ~Wr.get_str, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (LAWireSpell.ws_and_tt(LawsBase.wire_fits(String.length(x)), True{}, Wire.wire_str_decoded_fits(s, x, s3, er), {==}), {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      ws_fl_step(x, k, Wire.wire_str_decoded_fits(s, x, s3, er),
        Wr.get_list.go(~String, ~Wr.get_str, k, Wr.get_str(s3)), ws_fl_spec(k, Wr.get_str(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder answer says: the list fits
def ws_ff(d: Wr.Dec<List<&2, String>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {LawsBase.wire_strs_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ws_ff_conv(-m: Nat, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, String>>, fl: ws_fl(m, d)) -> ws_ff(d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = fl
      %Equal.sym(Nat, List.length(&2, String, xs), 1n+m, e2) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_strs_all(xs)) == True{} : Bool}
      LAWireSpell.ws_and_tt(LawsBase.wire_fits(1n+m), LawsBase.wire_strs_all(xs), hn, e1)
    case Wr.Bad{}:
      Unit{}

def ws_ff_nat(n: Nat, +s2: String, hn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  ws_ff(Wr.get_list.start(~String, ~Wr.get_str, Wr.Got{n, s2})):
  match n:
    case 0n:
      {==}
    case 1n++m:
      ws_ff_conv(m, hn, Wr.get_list.go(~String, ~Wr.get_str, m, Wr.get_str(s2)), ws_fl_spec(m, Wr.get_str(s2), s2, {==}))

def ws_ff_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) ->
  ws_ff(Wr.get_list.start(~String, ~Wr.get_str, r)):
  match r:
    case Wr.Got{+n, +s2}:
      ws_ff_nat(n, s2, Wire.wire_nat_decoded_fits(s, n, s2, er))
    case Wr.Bad{}:
      Unit{}

def Wire.wire_strs_decoded_fit(s, xs, rest, h):
  %h : ws_ff(_)
  ws_ff_top(s, Wr.get_nat(s), {==})
