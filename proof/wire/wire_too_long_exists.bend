# eukhe: the proof of LAW wire_too_long_exists

import Base
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/list.bend as LList
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/list.bend as LLogicList
import ../base/logic/nat.bend as LLogicNat
import ./base.bend as LA

# a canonical list fits the wire as its length does
def wn_fits_len(+t: List<&2, Nat>, +d: Nat, +c: {LLogicBool.wn_okc(t, d) == True{} : Bool})
  -> {LawsBase.wire_fits(LLogicNat.wo_value(d <> t)) == Nat.is_le(List.length(&2, Nat, d <> t), 14n) : Bool}:
  %Equal.sym(Nat, LawsBase.wire_digits(LLogicNat.wo_value(d <> t)), List.length(&2, Nat, LLogicList.wn_full(LLogicNat.wo_value(d <> t))), LList.wn_wl(LLogicNat.wo_value(d <> t))) : {Nat.is_le(_, 14n) == Nat.is_le(List.length(&2, Nat, d <> t), 14n) : Bool}
  %Equal.sym(List<&2, Nat>, LLogicList.wn_full(LLogicNat.wo_value(d <> t)), d <> t, LA.wn_lv(t, d, c)) : {Nat.is_le(List.length(&2, Nat, _), 14n) == Nat.is_le(List.length(&2, Nat, d <> t), 14n) : Bool}
  {==}

def Wire.wire_too_long_exists():
  (LLogicNat.wo_value([0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n]), Equal.trans(Bool, LawsBase.wire_fits(LLogicNat.wo_value([0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n])), Nat.is_le(List.length(&2, Nat, [0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n]), 14n), False{},
    wn_fits_len([0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n], 0n, {==}), {==}))
