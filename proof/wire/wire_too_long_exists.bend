# eukhe: the proof of LAW wire_too_long_exists

import Base
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/bool/misc.bend as LBoolMisc
import ../base/list.bend as LList
import ../base/nat/misc.bend as LNatMisc
import ./base.bend as LA

# a canonical list fits the wire as its length does
def wn_fits_len(+t: List<&2, Nat>, +d: Nat, +c: {LBoolMisc.wn_okc(t, d) == True{} : Bool})
  -> {LawsBase.wire_fits(LNatMisc.wo_value(d <> t)) == Nat.is_le(List.length(&2, Nat, d <> t), 14n) : Bool}:
  %Equal.sym(Nat, LawsBase.wire_digits(LNatMisc.wo_value(d <> t)), List.length(&2, Nat, LList.wn_full(LNatMisc.wo_value(d <> t))), LList.wn_wl(LNatMisc.wo_value(d <> t))) : {Nat.is_le(_, 14n) == Nat.is_le(List.length(&2, Nat, d <> t), 14n) : Bool}
  %Equal.sym(List<&2, Nat>, LList.wn_full(LNatMisc.wo_value(d <> t)), d <> t, LA.wn_lv(t, d, c)) : {Nat.is_le(List.length(&2, Nat, _), 14n) == Nat.is_le(List.length(&2, Nat, d <> t), 14n) : Bool}
  {==}

def Wire.wire_too_long_exists():
  (LNatMisc.wo_value([0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n]), Equal.trans(Bool, LawsBase.wire_fits(LNatMisc.wo_value([0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n])), Nat.is_le(List.length(&2, Nat, [0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n]), 14n), False{},
    wn_fits_len([0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n], 0n, {==}), {==}))
