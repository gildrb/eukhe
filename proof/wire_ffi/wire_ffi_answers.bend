# eukhe: the proof of LAW wire_ffi_answers
#
# PROOF: the laws' list spelling is the wire's (wire_nats_spells); then each
# field reads back by its round trip law, the rest untouched, and the entry
# writes the same fields again with the wire's encoders.

import Base
import ../../bend/ffi_wire.bend as FWi
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/wire_ffi.bend as WireFfi
import ../base/wire.bend as LBaseWire
import ../wire/wire_u32_round_trip.bend as PWireU32RoundTrip
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ./base.bend as LA

def wa.fields(+n: Nat, +x: U32, +b: Bool, +a: String, +xs: List<&2, Nat>, fn: {LawsBase.wire_fits(n) == True{} : Bool}, fa: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}, fl: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}) -> {FWi.ffi(Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, Wr.put_str(a, Wr.put_list(~Nat, ~Wr.put_nat, xs, "")))))) == Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, Wr.put_str(a, Wr.put_list(~Nat, ~Wr.put_nat, xs, ""))))) : String}:
  +l = Wr.put_list(~Nat, ~Wr.put_nat, xs, "")
  +r3 = Wr.put_str(a, l)
  +r2 = Wr.put_bool(b, r3)
  +r1 = Wr.put_u32(x, r2)
  %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, r1)), Wr.Got{n, r1}, Wire.wire_nat_round_trip(n, r1, fn)) : {FWi.at.nat(_) == Wr.put_nat(n, r1) : String}
  %Equal.sym(Wr.Dec<U32>, Wr.get_u32(r1), Wr.Got{x, r2}, Wire.wire_u32_round_trip(x, r2)) : {FWi.at.u32(_, n) == Wr.put_nat(n, r1) : String}
  %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r2), Wr.Got{b, r3}, Wire.wire_bool_round_trip(b, r3)) : {FWi.at.bool(_, n, x) == Wr.put_nat(n, r1) : String}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(r3), Wr.Got{a, l}, Wire.wire_str_round_trip(a, l, fa)) : {FWi.at.str(_, n, x, b) == Wr.put_nat(n, r1) : String}
  %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, l), Wr.Got{xs, ""}, Wire.wire_list_round_trip(xs, "", fl)) : {FWi.at.end(_, n, x, b, a) == Wr.put_nat(n, r1) : String}
  {==}

def wa.go(+q: WireFfi.wr.Req, +fits: {WireFfi.wr_fits(q) == True{} : Bool}) -> {FWi.ffi(WireFfi.wr_spell(q, "")) == WireFfi.wr_spell(q, "") : String}:
  match q:
    case WireFfi.wr.Req{+n, +x, +b, +a, +xs}:
      +fr = LA.wrb.and_r(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(String.length(a)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))), fits)
      %Wire.wire_nats_spells(xs, "") : {FWi.ffi(Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, Wr.put_str(a, _))))) == Wr.put_nat(n, Wr.put_u32(x, Wr.put_bool(b, Wr.put_str(a, _)))) : String}
      wa.fields(n, x, b, a, xs, LA.wrb.and_l(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(String.length(a)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs))), fits), LA.wrb.and_l(LawsBase.wire_fits(String.length(a)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)), fr), LA.wrb.and_r(LawsBase.wire_fits(String.length(a)), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)), fr))

def WireFfi.wire_ffi_answers(q, fits):
  wa.go(q, fits)
