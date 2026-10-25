# eukhe: the proof of LAW wire_str_decoded_fits
#
# PROOF of LAW wire_str_decoded_fits: a decoded string is the n chars
# after its length n (wr_take_spec of wire_str_exact), and a decoded Nat
# fits (wire_nat_decoded_fits), so its length fits.

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/wire.bend as LLogicWire
import ../base/wire.bend as LWire
import ./wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ./wire_str_exact.bend as PWireStrExact

# what a string decoder answer says: its string fits
def ws_fits_of(d: Wr.Dec<String>) -> Type:
  match d:
    case Wr.Got{+a, r}:
      {LawsBase.wire_fits(String.length(a)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ws_fits_conv(-n: Nat, hn: {LawsBase.wire_fits(n) == True{} : Bool}, -s2: String, d: Wr.Dec<String>, pt: PWireStrExact.wr_pt(s2, n, d)) -> ws_fits_of(d):
  match d:
    case Wr.Got{+a, +r}:
      (e1, e2) = pt
      %Equal.sym(Nat, String.length(a), n, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
      hn
    case Wr.Bad{}:
      Unit{}

def ws_fits_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) -> ws_fits_of(Wr.get_str.go(r)):
  match r:
    case Wr.Got{+n, +s2}:
      %Equal.sym(Wr.Dec<String>, Wr.take(n, s2), LLogicWire.wo_take(n, s2), LWire.wr_take_eq(n, s2)) : ws_fits_of(_)
      ws_fits_conv(n, Wire.wire_nat_decoded_fits(s, n, s2, er), s2, LLogicWire.wo_take(n, s2), PWireStrExact.wr_take_spec(n, s2))
    case Wr.Bad{}:
      Unit{}

def Wire.wire_str_decoded_fits(s, a, rest, h):
  %h : ws_fits_of(_)
  ws_fits_top(s, Wr.get_nat(s), {==})
