# eukhe: the proof of LAW effort_open_fits
#
# sf.fit: a level fitted by effort_fits is the model's fit of it. Without a
# catalog model the ranks agree, so the levels do; with one, either the
# clamp lands where effort_lands says (CN.cn.near_clamp), or the model offers
# none and the clamp is off (LA.pe.clamp_nil). Open stores the fit of the
# stored level, else of the default.

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA
import ./effort_clamp_up_first.bend as CN

# the level of a rank
def sf.of_rank(l: Ef.Lv) -> {LA.pe.of(Effort.effort_rank(l)) == l : Ef.Lv}:
  match l:
    case Ef.Off{}:
      {==}
    case Ef.Minimal{}:
      {==}
    case Ef.Low{}:
      {==}
    case Ef.Medium{}:
      {==}
    case Ef.High{}:
      {==}
    case Ef.Xhigh{}:
      {==}
    case Ef.Max{}:
      {==}

# levels of one rank are one level
def sf.same(+l: Ef.Lv, +k: Ef.Lv, h: {Nat.is_eq(Effort.effort_rank(l), Effort.effort_rank(k)) == True{} : Bool}) -> {l == k : Ef.Lv}:
  +r = LA.pe.eq_true(Effort.effort_rank(l), Effort.effort_rank(k), h)
  +a = Equal.sym(Ef.Lv, LA.pe.of(Effort.effort_rank(l)), l, sf.of_rank(l))
  +b = Equal.cong(Nat, Ef.Lv, n => LA.pe.of(n), Effort.effort_rank(l), Effort.effort_rank(k), r)
  Equal.trans(Ef.Lv, l, LA.pe.of(Effort.effort_rank(k)), k, Equal.trans(Ef.Lv, l, LA.pe.of(Effort.effort_rank(l)), LA.pe.of(Effort.effort_rank(k)), a, b), sf.of_rank(k))

# a list of no levels is empty
def sf.nil(lad: List<&2, Ef.Lv>, h: {Nat.is_eq(List.length(&2, Ef.Lv, lad), 0n) == True{} : Bool}) -> {lad == [] : List<&2, Ef.Lv>}:
  match lad:
    case Nil{}:
      {==}
    case x <> rest:
      LA.pe.absurdF({x <> rest == [] : List<&2, Ef.Lv>}, h)

def sf.of_at(b: Bool, +lad: List<&2, Ef.Lv>, +l: Ef.Lv, +k: Ef.Lv, eb: {Effort.effort_lands(lad, l, k) == b : Bool}, +h: {Bool.or(b, Bool.and(Nat.is_eq(List.length(&2, Ef.Lv, lad), 0n), Nat.is_eq(Effort.effort_rank(k), 0n))) == True{} : Bool}) -> {Ef.clamp.in(lad, l) == k : Ef.Lv}:
  match b:
    case True{}:
      CN.cn.near_clamp(lad, l, k, eb)
    case False{}:
      +h0 = LA.pe.and_l(Nat.is_eq(List.length(&2, Ef.Lv, lad), 0n), Nat.is_eq(Effort.effort_rank(k), 0n), h)
      +hk = LA.pe.and_r(Nat.is_eq(List.length(&2, Ef.Lv, lad), 0n), Nat.is_eq(Effort.effort_rank(k), 0n), h)
      %Equal.sym(List<&2, Ef.Lv>, lad, [], sf.nil(lad, h0)) : {Ef.clamp.in(_, l) == k : Ef.Lv}
      %Equal.sym(Ef.Lv, k, Ef.Off{}, sf.same(k, Ef.Off{}, hk)) : {Ef.clamp.in([], l) == _ : Ef.Lv}
      LA.pe.clamp_nil(l)

# a level fitted by effort_fits is the model's fit of it
def sf.fit(mo: Maybe<&2, Ef.Mdl>, +l: Ef.Lv, +k: Ef.Lv, h: {Effort.effort_fits(mo, l, k) == True{} : Bool}) -> {Ef.fit(mo, l) == k : Ef.Lv}:
  match mo:
    case None{}:
      sf.same(l, k, h)
    case Some{+m}:
      sf.of_at(Effort.effort_lands(Ef.offered(m), l, k), Ef.offered(m), l, k, {==}, h)

# the session with level v stored
def sf.with(+mo: Maybe<&2, Ef.Mdl>, v: Ef.Lv) -> Ef.Sess:
  Ef.Sess{mo, Some{v}}

def Effort.effort_open_fits(mo, st, dflt, k, fit):
  Equal.cong(Ef.Lv, Ef.Sess, v => sf.with(mo, v), Ef.fit(mo, Maybe.default(&2, Ef.Lv, st, dflt)), k, sf.fit(mo, Maybe.default(&2, Ef.Lv, st, dflt), k, fit))
