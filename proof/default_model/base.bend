# eukhe: lemmas the proofs of area default_model share

import Base
import ../../bend/default_model.bend as Dm
import ../../bend/ffi_default_model.bend as FDm
import ../../bend/wire.bend as Wr
import ../../laws/default_model.bend as DefaultModel
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base.bend as L
import ../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ./dmw_reason_round_trip.bend as PDmwReasonRoundTrip

# ---- default_model_wire ----

# Place after PROOF.bend section wire: the proofs use its Laws.wire_*
# fills and wr_and_l / wr_and_r.

# a Nat that fits reads back (Laws.wire_nat_round_trip, turned around)
def pdw.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

# a Bool reads back (Laws.wire_bool_round_trip, turned around)
def pdw.bool(+b: Bool, +rest: String) -> {Wr.Got{b, rest} == Wr.get_bool(Wr.put_bool(b, rest)) : Wr.Dec<Bool>}:
  Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(b, rest)), Wr.Got{b, rest}, Wire.wire_bool_round_trip(b, rest))

# a reason reads back (turned around for rewriting)
def pdw.reason(+r: Dm.Reason, +rest: String) -> {Wr.Got{r, rest} == FDm.get_reason(FDm.put_reason(r, rest)) : Wr.Dec<Dm.Reason>}:
  Equal.sym(Wr.Dec<Dm.Reason>, FDm.get_reason(FDm.put_reason(r, rest)), Wr.Got{r, rest}, DefaultModel.dmw_reason_round_trip(r, rest))

def DefaultModel.dmw_saved_round_trip(x, rest, h):
  match x:
    case Dm.NoDefault{}:
      {==}
    case Dm.Default{+m}:
      %pdw.nat(m, rest, h) : {FDm.get_saved.m(_) == Wr.Got{Dm.Default{m}, rest} : Wr.Dec<Dm.Saved>}
      {==}

# a saved reads back (turned around for rewriting)
def pdw.saved(+x: Dm.Saved, +rest: String, h: {DefaultModel.dmw_saved_fits(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FDm.get_saved(FDm.put_saved(x, rest)) : Wr.Dec<Dm.Saved>}:
  Equal.sym(Wr.Dec<Dm.Saved>, FDm.get_saved(FDm.put_saved(x, rest)), Wr.Got{x, rest}, DefaultModel.dmw_saved_round_trip(x, rest, h))

def DefaultModel.dmw_next_round_trip(x, rest, h):
  match x:
    case Dm.NoNext{}:
      {==}
    case Dm.Next{+n}:
      %pdw.nat(n, rest, h) : {FDm.get_next.n(_) == Wr.Got{Dm.Next{n}, rest} : Wr.Dec<Dm.Next>}
      {==}

# a next reads back (turned around for rewriting)
def pdw.next(+x: Dm.Next, +rest: String, h: {DefaultModel.dmw_next_fits(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FDm.get_next(FDm.put_next(x, rest)) : Wr.Dec<Dm.Next>}:
  Equal.sym(Wr.Dec<Dm.Next>, FDm.get_next(FDm.put_next(x, rest)), Wr.Got{x, rest}, DefaultModel.dmw_next_round_trip(x, rest, h))

def DefaultModel.dmw_in_round_trip(x, rest, h):
  match x:
    case Dm.In{+saved, +cat, +key, +out, +next}:
      +z = rest
      +hh = h
      %pdw.saved(saved, Wr.put_bool(cat, Wr.put_bool(key, Wr.put_bool(out, FDm.put_next(next, z)))), L.wr_and_l(DefaultModel.dmw_saved_fits(saved), DefaultModel.dmw_next_fits(next), hh)) : {FDm.get_in.go(_) == Wr.Got{Dm.In{saved, cat, key, out, next}, z} : Wr.Dec<Dm.In>}
      %pdw.bool(cat, Wr.put_bool(key, Wr.put_bool(out, FDm.put_next(next, z)))) : {FDm.get_in.cat(saved, _) == Wr.Got{Dm.In{saved, cat, key, out, next}, z} : Wr.Dec<Dm.In>}
      %pdw.bool(key, Wr.put_bool(out, FDm.put_next(next, z))) : {FDm.get_in.key(saved, cat, _) == Wr.Got{Dm.In{saved, cat, key, out, next}, z} : Wr.Dec<Dm.In>}
      %pdw.bool(out, FDm.put_next(next, z)) : {FDm.get_in.out(saved, cat, key, _) == Wr.Got{Dm.In{saved, cat, key, out, next}, z} : Wr.Dec<Dm.In>}
      %pdw.next(next, z, L.wr_and_r(DefaultModel.dmw_saved_fits(saved), DefaultModel.dmw_next_fits(next), hh)) : {FDm.get_in.next(saved, cat, key, out, _) == Wr.Got{Dm.In{saved, cat, key, out, next}, z} : Wr.Dec<Dm.In>}
      {==}

# a in reads back (turned around for rewriting)
def pdw.in(+x: Dm.In, +rest: String, h: {DefaultModel.dmw_in_fits(x) == True{} : Bool}) -> {Wr.Got{x, rest} == FDm.get_in(FDm.put_in(x, rest)) : Wr.Dec<Dm.In>}:
  Equal.sym(Wr.Dec<Dm.In>, FDm.get_in(FDm.put_in(x, rest)), Wr.Got{x, rest}, DefaultModel.dmw_in_round_trip(x, rest, h))

def DefaultModel.dmw_key_round_trip(k, rest, h):
  match k:
    case Dm.K{+m, +r}:
      +z = rest
      %pdw.nat(m, FDm.put_reason(r, z), h) : {FDm.get_key.go(_) == Wr.Got{Dm.K{m, r}, z} : Wr.Dec<Dm.Key>}
      %pdw.reason(r, z) : {FDm.get_key.r(m, _) == Wr.Got{Dm.K{m, r}, z} : Wr.Dec<Dm.Key>}
      {==}

# a key reads back (turned around for rewriting)
def pdw.key(+k: Dm.Key, +rest: String, h: {DefaultModel.dmw_key_fits(k) == True{} : Bool}) -> {Wr.Got{k, rest} == FDm.get_key(FDm.put_key(k, rest)) : Wr.Dec<Dm.Key>}:
  Equal.sym(Wr.Dec<Dm.Key>, FDm.get_key(FDm.put_key(k, rest)), Wr.Got{k, rest}, DefaultModel.dmw_key_round_trip(k, rest, h))
