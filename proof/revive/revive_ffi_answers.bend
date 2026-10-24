# eukhe: the proof of LAW revive_ffi_answers
# The request's Bools and numbers read back (the wire's round trips,
# Wire.wire_bool_round_trip and LWire.pw6.nat); the entry's veto put on the
# wire is the spec's reply (LRv.rvb.reply: its freshness is the spec's).

import Base
import ../../bend/ffi_revive.bend as FR
import ../../bend/revive.bend as Rv
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/revive.bend as Revive
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire
import ./base.bend as LRv
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip

# a Bool reads back (turned around for rewriting)
def rfa.bool(+b: Bool, +rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest))

# a spelled lease reads back
def rfa.lease(l: Maybe<&2, Nat>, +r: String, h: {Revive.rv_lease_fits(l) == True{} : Bool}) -> {Wr.Got{l, r} == FR.get_lease(Wr.get_nat(Revive.rv_spell_lease(l, r))) : Wr.Dec<Maybe<&2, Nat>>}:
  match l:
    case None{}:
      %LWire.pw6.nat(0n, r, {==}) : {Wr.Got{None{}, r} == FR.get_lease(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}
    case Some{+p}:
      %LWire.pw6.nat(1n, Wr.put_nat(p, r), {==}) : {Wr.Got{Some{p}, r} == FR.get_lease(_) : Wr.Dec<Maybe<&2, Nat>>}
      %LWire.pw6.nat(p, r, h) : {Wr.Got{Some{p}, r} == FR.get_lease.pid(_) : Wr.Dec<Maybe<&2, Nat>>}
      {==}

# a spelled busy record reads back
def rfa.busy(b: Rv.Busy, +r: String, h: {Revive.rv_busy_fits(b) == True{} : Bool}) -> {Wr.Got{b, r} == FR.get_busy(Wr.get_nat(Revive.rv_spell_busy(b, r))) : Wr.Dec<Rv.Busy>}:
  match b:
    case Rv.NoBusy{}:
      %LWire.pw6.nat(0n, r, {==}) : {Wr.Got{Rv.NoBusy{}, r} == FR.get_busy(_) : Wr.Dec<Rv.Busy>}
      {==}
    case Rv.Unread{}:
      %LWire.pw6.nat(1n, r, {==}) : {Wr.Got{Rv.Unread{}, r} == FR.get_busy(_) : Wr.Dec<Rv.Busy>}
      {==}
    case Rv.Stamp{+at}:
      %LWire.pw6.nat(2n, Wr.put_nat(at, r), {==}) : {Wr.Got{Rv.Stamp{at}, r} == FR.get_busy(_) : Wr.Dec<Rv.Busy>}
      %LWire.pw6.nat(at, r, h) : {Wr.Got{Rv.Stamp{at}, r} == FR.get_busy.at(_) : Wr.Dec<Rv.Busy>}
      {==}

def rfa.go(+fl: Bool, +a: Bool, +l: Maybe<&2, Nat>, +b: Rv.Busy, +n: Nat, +m: Nat, +k: Nat,
  hl: {Revive.rv_lease_fits(l) == True{} : Bool}, hb: {Revive.rv_busy_fits(b) == True{} : Bool},
  hn: {LawsBase.wire_fits(n) == True{} : Bool}, hm: {LawsBase.wire_fits(m) == True{} : Bool}, hk: {LawsBase.wire_fits(k) == True{} : Bool})
  -> {FR.ffi(Revive.rv_spell(Rv.Facts{fl, a, l, b, n, m, k})) == Revive.rv_reply(Rv.Facts{fl, a, l, b, n, m, k}) : String}:
  +r4 = Wr.put_nat(n, Wr.put_nat(m, Wr.put_nat(k, "")))
  +r3 = Revive.rv_spell_busy(b, r4)
  +r2 = Revive.rv_spell_lease(l, r3)
  +g = Revive.rv_reply(Rv.Facts{fl, a, l, b, n, m, k})
  %rfa.bool(fl, Wr.put_bool(a, r2)) : {FR.ffi.go(FR.get_facts.archived(_)) == g : String}
  %rfa.bool(a, r2) : {FR.ffi.go(FR.get_facts.lease(fl, _)) == g : String}
  %rfa.lease(l, r3, hl) : {FR.ffi.go(FR.get_facts.busy(fl, a, _)) == g : String}
  %rfa.busy(b, r4, hb) : {FR.ffi.go(FR.get_facts.now(fl, a, l, _)) == g : String}
  %LWire.pw6.nat(n, Wr.put_nat(m, Wr.put_nat(k, "")), hn) : {FR.ffi.go(FR.get_facts.now.n(fl, a, l, b, _)) == g : String}
  %LWire.pw6.nat(m, Wr.put_nat(k, ""), hm) : {FR.ffi.go(FR.get_facts.max(fl, a, l, b, n, _)) == g : String}
  %LWire.pw6.nat(k, "", hk) : {FR.ffi.go(FR.get_facts.skew(fl, a, l, b, n, m, _)) == g : String}
  LRv.rvb.reply(Rv.Facts{fl, a, l, b, n, m, k})

def Revive.revive_ffi_answers(f, fits):
  match f:
    case Rv.Facts{fl, a, l, b, n, m, k}:
      +h = fits
      +hl = LLogicBool.wr_and_l(Revive.rv_lease_fits(l), Bool.and(Revive.rv_busy_fits(b), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(k)))), h)
      +h1 = LLogicBool.wr_and_r(Revive.rv_lease_fits(l), Bool.and(Revive.rv_busy_fits(b), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(k)))), h)
      +hb = LLogicBool.wr_and_l(Revive.rv_busy_fits(b), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(k))), h1)
      +h2 = LLogicBool.wr_and_r(Revive.rv_busy_fits(b), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(k))), h1)
      +hn = LLogicBool.wr_and_l(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(k)), h2)
      +h3 = LLogicBool.wr_and_r(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(k)), h2)
      +hm = LLogicBool.wr_and_l(LawsBase.wire_fits(m), LawsBase.wire_fits(k), h3)
      +hk = LLogicBool.wr_and_r(LawsBase.wire_fits(m), LawsBase.wire_fits(k), h3)
      rfa.go(fl, a, l, b, n, m, k, hl, hb, hn, hm, hk)
