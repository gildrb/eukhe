# eukhe: the proof of LAW wire_fits_digits
#
# PROOF: one digit computes; a numeral of two digits or more is a
# canonical digit list (wnm.okc_from), the digits of its value are that
# list (wn_lv), and wire_digits counts the digits of a value (wn_wl).

import Base
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/list.bend as LList
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/list.bend as LLogicList
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/nat.bend as LLogicNat
import ./base.bend as LAWire
import ./base/numeral.bend as LWireNum

# one digit
def wfd.one(d: Nat, h: {Nat.is_lt(d, 10n) == True{} : Bool}) -> {LawsBase.wire_fits(Wire.wire_value([d])) == Nat.is_le(List.length(&2, Nat, [d]), 14n) : Bool}:
  match d:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+p:
      match p:
        case 0n:
          LLogicLogic.wn_absurd({LawsBase.wire_fits(Wire.wire_value([10n])) == Nat.is_le(List.length(&2, Nat, [10n]), 14n) : Bool}, h)
        case 1n+q:
          LLogicLogic.wn_absurd({LawsBase.wire_fits(Wire.wire_value([11n+q])) == Nat.is_le(List.length(&2, Nat, [11n+q]), 14n) : Bool}, h)

# a canonical digit list
def wfd.canon(+t: List<&2, Nat>, +d: Nat, +c: {LLogicBool.wn_okc(t, d) == True{} : Bool}) -> {LawsBase.wire_fits(Wire.wire_value(d <> t)) == Nat.is_le(List.length(&2, Nat, d <> t), 14n) : Bool}:
  +v = LLogicNat.wo_value(d <> t)
  +e1 = Equal.cong(Nat, Bool, x => LawsBase.wire_fits(x), Wire.wire_value(d <> t), v, LWireNum.wnm.value(d <> t))
  +e2 = Equal.cong(Nat, Bool, x => Nat.is_le(x, 14n), LawsBase.wire_digits(v), List.length(&2, Nat, LLogicList.wn_full(v)), LList.wn_wl(v))
  +e3 = Equal.cong(List<&2, Nat>, Bool, x => Nat.is_le(List.length(&2, Nat, x), 14n), LLogicList.wn_full(v), d <> t, LAWire.wn_lv(t, d, c))
  Equal.trans(Bool, LawsBase.wire_fits(Wire.wire_value(d <> t)), LawsBase.wire_fits(v), Nat.is_le(List.length(&2, Nat, d <> t), 14n), e1,
    Equal.trans(Bool, LawsBase.wire_fits(v), Nat.is_le(List.length(&2, Nat, LLogicList.wn_full(v)), 14n), Nat.is_le(List.length(&2, Nat, d <> t), 14n), e2, e3))

def wfd.from(t: List<&2, Nat>, +d: Nat, +h: {Wire.wire_numeral.from(d, t) == True{} : Bool}) -> {LawsBase.wire_fits(Wire.wire_value(d <> t)) == Nat.is_le(List.length(&2, Nat, d <> t), 14n) : Bool}:
  match t:
    case Nil{}:
      wfd.one(d, h)
    case Con{+e, +u}:
      wfd.canon(e <> u, d, LWireNum.wnm.okc_from(d, e, u, h))

def Wire.wire_fits_digits(ds, h):
  match ds:
    case Nil{}:
      LLogicLogic.wn_absurd({LawsBase.wire_fits(Wire.wire_value(Nil{})) == Nat.is_le(List.length(&2, Nat, Nil{}), 14n) : Bool}, h)
    case Con{+d, +t}:
      wfd.from(t, d, h)
