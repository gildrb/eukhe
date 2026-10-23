# eukhe: lemmas the proofs of area admission share: wire

import Base
import ../../../bend/admission.bend as Ad
import ../../../bend/ffi_admission.bend as FAd
import ../../../bend/wire.bend as Wr
import ../../../laws/admission.bend as Admission
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../base/bool/and.bend as LBoolAnd
import ../../base/wire.bend as LWire
import ../adw_cls_round_trip.bend as PAdwClsRoundTrip

# ---- admission_wire ----

# Place after PROOF.bend section wire: the proofs use its Laws.wire_*
# fills and wr_and_l / wr_and_r.

# a Nat that fits reads back (Laws.wire_nat_round_trip, turned around)
def paw.nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def Admission.adw_lim_round_trip(l, rest, h):
  match l:
    case Ad.Unl{}:
      {==}
    case Ad.Cap{+p}:
      %paw.nat(p, rest, h) : {FAd.get_lim.cap(_) == Wr.Got{Ad.Cap{p}, rest} : Wr.Dec<Ad.Lim>}
      {==}

# a cls reads back (turned around for rewriting)
def paw.cls(+c: Ad.Cls, +rest: String) -> {Wr.Got{c, rest} == FAd.get_cls(FAd.put_cls(c, rest)) : Wr.Dec<Ad.Cls>}:
  Equal.sym(Wr.Dec<Ad.Cls>, FAd.get_cls(FAd.put_cls(c, rest)), Wr.Got{c, rest}, Admission.adw_cls_round_trip(c, rest))

# a lim reads back (turned around for rewriting)
def paw.lim(+l: Ad.Lim, +rest: String, h: {Admission.adw_lim_fits(l) == True{} : Bool}) -> {Wr.Got{l, rest} == FAd.get_lim(FAd.put_lim(l, rest)) : Wr.Dec<Ad.Lim>}:
  Equal.sym(Wr.Dec<Ad.Lim>, FAd.get_lim(FAd.put_lim(l, rest)), Wr.Got{l, rest}, Admission.adw_lim_round_trip(l, rest, h))

def Admission.adw_op_round_trip(o, rest, h):
  match o:
    case Ad.Admit{+c}:
      %paw.cls(c, rest) : {FAd.get_op.admit(_) == Wr.Got{Ad.Admit{c}, rest} : Wr.Dec<Ad.Op>}
      {==}
    case Ad.Collect{+k}:
      %paw.nat(k, rest, h) : {FAd.get_op.k(_, 0n) == Wr.Got{Ad.Collect{k}, rest} : Wr.Dec<Ad.Op>}
      {==}
    case Ad.Release{+k}:
      %paw.nat(k, rest, h) : {FAd.get_op.k(_, 1n) == Wr.Got{Ad.Release{k}, rest} : Wr.Dec<Ad.Op>}
      {==}
    case Ad.Leave{+k}:
      %paw.nat(k, rest, h) : {FAd.get_op.k(_, 2n) == Wr.Got{Ad.Leave{k}, rest} : Wr.Dec<Ad.Op>}
      {==}
    case Ad.Limit{+l, +q}:
      +r = rest
      +hh = h
      %paw.lim(l, Wr.put_nat(q, r), LBoolAnd.wr_and_l(Admission.adw_lim_fits(l), LawsBase.wire_fits(q), hh)) : {FAd.get_op.limit(_) == Wr.Got{Ad.Limit{l, q}, r} : Wr.Dec<Ad.Op>}
      %paw.nat(q, r, LBoolAnd.wr_and_r(Admission.adw_lim_fits(l), LawsBase.wire_fits(q), hh)) : {FAd.get_op.q(l, _) == Wr.Got{Ad.Limit{l, q}, r} : Wr.Dec<Ad.Op>}
      {==}

# a op reads back (turned around for rewriting)
def paw.op(+o: Ad.Op, +rest: String, h: {Admission.adw_op_fits(o) == True{} : Bool}) -> {Wr.Got{o, rest} == FAd.get_op(FAd.put_op(o, rest)) : Wr.Dec<Ad.Op>}:
  Equal.sym(Wr.Dec<Ad.Op>, FAd.get_op(FAd.put_op(o, rest)), Wr.Got{o, rest}, Admission.adw_op_round_trip(o, rest, h))

def Admission.adw_open_round_trip(l, q, rest, h):
  +r = rest
  +hh = h
  %paw.lim(l, Wr.put_nat(q, r), LBoolAnd.wr_and_l(Admission.adw_lim_fits(l), LawsBase.wire_fits(q), hh)) : {FAd.get_open.go(_) == Wr.Got{(l, q), r} : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}
  %paw.nat(q, r, LBoolAnd.wr_and_r(Admission.adw_lim_fits(l), LawsBase.wire_fits(q), hh)) : {FAd.get_open.q(l, _) == Wr.Got{(l, q), r} : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}
  {==}

# an open request that fits reads back (turned around for rewriting)
def paw.open(+l: Ad.Lim, +q: Nat, +rest: String, h: {Bool.and(Admission.adw_lim_fits(l), LawsBase.wire_fits(q)) == True{} : Bool}) ->
  {Wr.Got{(l, q), rest} == FAd.get_open(FAd.put_lim(l, Wr.put_nat(q, rest))) : Wr.Dec<+Sigma<Ad.Lim, x => Nat>>}:
  Equal.sym(Wr.Dec<+Sigma<Ad.Lim, x => Nat>>, FAd.get_open(FAd.put_lim(l, Wr.put_nat(q, rest))), Wr.Got{(l, q), rest}, Admission.adw_open_round_trip(l, q, rest, h))
