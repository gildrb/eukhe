# eukhe: the proof of LAW wire_nat_spells_digits
#
# PROOF: the numeral of n is its digit list, lowest first (wn_full): 0 is
# the one digit 0 (computes); any other n's list is canonical (wn_cf, so a
# numeral: wnm.from), worth n (wn_vf), and put_nat emits it highest first
# (wn_put_emit), each digit's char the char of code 48 + the digit
# (wnm.emit).

import Base
import ../../bend/wire.bend as Wr
import ../../laws/wire.bend as Wire
import ../base/logic/list.bend as LLogicList
import ../base/logic/nat.bend as LLogicNat
import ../base/logic/string.bend as LLogicString
import ../base/pair.bend as LPair
import ../base/wire.bend as LWire
import ./base/numeral.bend as LWireNum

# three equations make one
def wsd.tri(-a1: Bool, -a2: Bool, -b1: Nat, -b2: Nat, -c1: String, -c2: String, ea: {a1 == a2 : Bool}, eb: {b1 == b2 : Nat}, ec: {c1 == c2 : String}) -> {(a1, (b1, c1)) == (a2, (b2, c2)) : Bool & (Nat & String)}:
  %ea : {(a1, (b1, c1)) == (_, (b2, c2)) : Bool & (Nat & String)}
  %eb : {(a1, (b1, c1)) == (a1, (_, c2)) : Bool & (Nat & String)}
  %ec : {(a1, (b1, c1)) == (a1, (b1, _)) : Bool & (Nat & String)}
  {==}

def Wire.wire_nat_spells_digits(n, rest):
  match n:
    case 0n:
      ([0n], {==})
    case 1n++p:
      +r = rest
      +m = {1n+p : Nat}
      +d = Nat.mod(m, 10n)
      +t = LLogicList.wn_L(m, Nat.div(m, 10n))
      +c = LPair.wn_cf(p)
      +acc = {SCon{',', r} : String}
      +ev = Equal.trans(Nat, Wire.wire_value(d <> t), LLogicNat.wo_value(d <> t), m, LWireNum.wnm.value(d <> t), LPair.wn_vf(m))
      +ep = Equal.trans(String, Wr.put_nat(m, r), LLogicString.wn_emit(d <> t, acc), Wire.wire_numeral_chars(d <> t, acc), LWire.wn_put_emit(m, r), LWireNum.wnm.emit(t, d, acc, c))
      (d <> t, wsd.tri(Wire.wire_numeral(d <> t), True{}, Wire.wire_value(d <> t), m, Wr.put_nat(m, r), Wire.wire_numeral_chars(d <> t, acc), LWireNum.wnm.from(t, d, c), ev, ep))
