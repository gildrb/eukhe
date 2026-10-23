# eukhe: the proof of LAW wire_too_long_exists

import Base
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

# a canonical list fits the wire as its length does
def wn_fits_len(+t: List<&2, Nat>, +d: Nat, +c: {L.wn_okc(t, d) == True{} : Bool})
  -> {Laws.wire_fits(L.wo_value(d <> t)) == Nat.is_le(List.length(&2, Nat, d <> t), 14n) : Bool}:
  %Equal.sym(Nat, Laws.wire_digits(L.wo_value(d <> t)), List.length(&2, Nat, L.wn_full(L.wo_value(d <> t))), L.wn_wl(L.wo_value(d <> t))) : {Nat.is_le(_, 14n) == Nat.is_le(List.length(&2, Nat, d <> t), 14n) : Bool}
  %Equal.sym(List<&2, Nat>, L.wn_full(L.wo_value(d <> t)), d <> t, LA.wn_lv(t, d, c)) : {Nat.is_le(List.length(&2, Nat, _), 14n) == Nat.is_le(List.length(&2, Nat, d <> t), 14n) : Bool}
  {==}

def Laws.wire_too_long_exists():
  (L.wo_value([0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n]), Equal.trans(Bool, Laws.wire_fits(L.wo_value([0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n])), Nat.is_le(List.length(&2, Nat, [0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n]), 14n), False{},
    wn_fits_len([0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 0n, 1n], 0n, {==}), {==}))
