# eukhe: the code's 4 MAD (bend/autoresearch/stats.bend conf.go) is the
# spec's (spec/autoresearch/stats.bend mad4), for the proof of LAW
# confidence_exact: metrics shifted by the smallest are the spec's
# integers moved by a constant, which neither sorting nor deviations see

import Base
import ../../../../bend/autoresearch/dec.bend as ArD
import ../../../../bend/autoresearch/stats.bend as ArT
import ../../../../spec/autoresearch/decimal.bend as SD
import ../../../../spec/autoresearch/stats.bend as SS
import ./nat.bend as CN
import ./big.bend as CB
import ./zint.bend as CZ
import ./order.bend as CO
import ./sort.bend as CS
import ./median.bend as CM

# Shifted metrics
# ---------------

# a metric's shifted integer is the smallest's plus its distance to it
def ac.o_shift(+K: Nat, +sc: Nat, +lo: ArD.Dec, +v: ArD.Dec, +glo: {CO.ac.good(K, sc, lo) == True{} : Bool}, +gv: {CO.ac.good(K, sc, v) == True{} : Bool}, +le: {Nat.is_le(CO.ac.o(K, sc, lo), CO.ac.o(K, sc, v)) == True{} : Bool}) -> {CO.ac.o(K, sc, v) == Nat.add(CO.ac.o(K, sc, lo), ArT.big.val(ArT.diff(v, lo, sc))) : Nat}:
  +c = CO.ac.o(K, sc, lo)
  +ov = CO.ac.o(K, sc, v)
  +e1 = Equal.trans(Nat, ArT.big.val(ArT.diff(v, lo, sc)), SS.z_dist(SS.z(v, sc), SS.z(lo, sc)), CB.ac.dist(ov, c), CZ.ac.diff_z(v, lo, sc, CO.ac.g_wf(K, sc, v, gv), CO.ac.g_wf(K, sc, lo, glo)), CZ.ac.z_dist_off(K, SS.z(v, sc), SS.z(lo, sc), CO.ac.g_rng(K, sc, v, gv), CO.ac.g_rng(K, sc, lo, glo)))
  +e2 = {%Equal.sym(Nat, Nat.sub(c, ov), 0n, CN.ac.sub_le(c, ov, le)) : {Nat.add(Nat.sub(ov, c), _) == Nat.sub(ov, c) : Nat}; CN.ac.add_zero(Nat.sub(ov, c)) : {CB.ac.dist(ov, c) == Nat.sub(ov, c) : Nat}}
  %Equal.sym(Nat, ArT.big.val(ArT.diff(v, lo, sc)), Nat.sub(ov, c), Equal.trans(Nat, ArT.big.val(ArT.diff(v, lo, sc)), CB.ac.dist(ov, c), Nat.sub(ov, c), e1, e2)) : {ov == Nat.add(c, _) : Nat}
  Equal.sym(Nat, Nat.add(c, Nat.sub(ov, c)), ov, CN.ac.add_sub(c, ov, le))

def ac.offs_shift(+K: Nat, +sc: Nat, +lo: ArD.Dec, vs: List<&2, ArD.Dec>, +glo: {CO.ac.good(K, sc, lo) == True{} : Bool}, +gs: {CO.ac.allgood(K, sc, vs) == True{} : Bool}, +ge: {CO.ac.ge(K, sc, vs, CO.ac.o(K, sc, lo)) == True{} : Bool}) -> {CS.ac.offs(K, SS.zs_of(vs, sc)) == CS.ac.addc(CO.ac.o(K, sc, lo), CS.ac.vals(ArT.shifted(vs, lo, sc))) : List<&2, Nat>}:
  match vs:
    case Nil{}:
      {==}
    case +v <> +t:
      +c = CO.ac.o(K, sc, lo)
      +gv = CN.ac.and_l(CO.ac.good(K, sc, v), CO.ac.allgood(K, sc, t), gs)
      +gt = CN.ac.and_r(CO.ac.good(K, sc, v), CO.ac.allgood(K, sc, t), gs)
      +lv = CN.ac.and_l(Nat.is_le(c, CO.ac.o(K, sc, v)), CO.ac.ge(K, sc, t, c), ge)
      +lt = CN.ac.and_r(Nat.is_le(c, CO.ac.o(K, sc, v)), CO.ac.ge(K, sc, t, c), ge)
      +rest = CS.ac.addc(c, CS.ac.vals(ArT.shifted(t, lo, sc)))
      %ac.offs_shift(K, sc, lo, t, glo, gt, lt) : {CO.ac.o(K, sc, v) <> CS.ac.offs(K, SS.zs_of(t, sc)) == Nat.add(c, ArT.big.val(ArT.diff(v, lo, sc))) <> _ : List<&2, Nat>}
      %ac.o_shift(K, sc, lo, v, glo, gv, lv) : {CO.ac.o(K, sc, v) <> CS.ac.offs(K, SS.zs_of(t, sc)) == _ <> CS.ac.offs(K, SS.zs_of(t, sc)) : List<&2, Nat>}
      {==}

def ac.dok_signs(c: Bool, +a: List<&2, Nat>, +b: List<&2, Nat>, +ha: {SD.digits_ok(a) == True{} : Bool}, +hb: {SD.digits_ok(b) == True{} : Bool}) -> {SD.digits_ok(ArT.diff.signs(c, a, b)) == True{} : Bool}:
  match c:
    case True{}:
      CB.ac.dok_diff(a, b, ha, hb)
    case False{}:
      CB.ac.dok_add(a, b, 0n, ha, hb, {==})

def ac.dok_diffd(+a: ArD.Dec, +b: ArD.Dec, +sc: Nat, +wa: {SD.Wf(a) == True{} : Bool}, +wb: {SD.Wf(b) == True{} : Bool}) -> {SD.digits_ok(ArT.diff(a, b, sc)) == True{} : Bool}:
  ac.dok_signs(Bool.not(Bool.xor(ArT.neg(a), ArT.neg(b))), ArT.mag(a, sc), ArT.mag(b, sc), CB.ac.dok_mag(a, sc, wa), CB.ac.dok_mag(b, sc, wb))

def ac.shifted_dok(+K: Nat, +sc: Nat, +lo: ArD.Dec, vs: List<&2, ArD.Dec>, +glo: {CO.ac.good(K, sc, lo) == True{} : Bool}, +gs: {CO.ac.allgood(K, sc, vs) == True{} : Bool}) -> {CS.ac.adok(ArT.shifted(vs, lo, sc)) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case +v <> +t:
      +gv = CN.ac.and_l(CO.ac.good(K, sc, v), CO.ac.allgood(K, sc, t), gs)
      +gt = CN.ac.and_r(CO.ac.good(K, sc, v), CO.ac.allgood(K, sc, t), gs)
      CN.ac.and_i(SD.digits_ok(ArT.diff(v, lo, sc)), CS.ac.adok(ArT.shifted(t, lo, sc)), ac.dok_diffd(v, lo, sc, CO.ac.g_wf(K, sc, v, gv), CO.ac.g_wf(K, sc, lo, glo)), ac.shifted_dok(K, sc, lo, t, glo, gt))

def ac.zs_rng(+K: Nat, +sc: Nat, vs: List<&2, ArD.Dec>, +gs: {CO.ac.allgood(K, sc, vs) == True{} : Bool}) -> {CS.ac.arng(K, SS.zs_of(vs, sc)) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case +v <> +t:
      +gv = CN.ac.and_l(CO.ac.good(K, sc, v), CO.ac.allgood(K, sc, t), gs)
      CN.ac.and_i(CZ.ac.rng(K, SS.z(v, sc)), CS.ac.arng(K, SS.zs_of(t, sc)), CO.ac.g_rng(K, sc, v, gv), ac.zs_rng(K, sc, t, CN.ac.and_r(CO.ac.good(K, sc, v), CO.ac.allgood(K, sc, t), gs)))

def ac.zs_len(vs: List<&2, ArD.Dec>, +sc: Nat) -> {CS.ac.zlen(SS.zs_of(vs, sc)) == SS.len(vs) : Nat}:
  match vs:
    case Nil{}:
      {==}
    case v <> +t:
      %ac.zs_len(t, sc) : {1n+CS.ac.zlen(SS.zs_of(t, sc)) == 1n+_ : Nat}
      {==}

# The MAD
# -------

def ac.nlen_NU(+K: Nat, +c: Nat, +NU: List<&2, Nat>, +zs: List<&2, SS.Z>, +n: Nat, +E1: {CS.ac.offs(K, zs) == CS.ac.addc(c, NU) : List<&2, Nat>}, +lz: {CS.ac.zlen(zs) == n : Nat}) -> {CS.ac.nlen(NU) == n : Nat}:
  %CS.ac.addc_len(c, NU) : {_ == n : Nat}
  %E1 : {CS.ac.nlen(_) == n : Nat}
  %Equal.sym(Nat, CS.ac.nlen(CS.ac.offs(K, zs)), CS.ac.zlen(zs), CS.ac.offs_len(K, zs)) : {_ == n : Nat}
  lz

def ac.lt_by(+i: Nat, +a: Nat, +b: Nat, +e: {a == b : Nat}, +h: {Nat.is_lt(i, b) == True{} : Bool}) -> {Nat.is_lt(i, a) == True{} : Bool}:
  %Equal.sym(Nat, a, b, e) : {Nat.is_lt(i, _) == True{} : Bool}
  h

# the code's 4 MAD, as a value, is the spec's
def ac.mad(+K: Nat, +sc: Nat, +base: ArD.Dec, +V: List<&2, ArD.Dec>, +gb: {CO.ac.good(K, sc, base) == True{} : Bool}, +gs: {CO.ac.allgood(K, sc, V) == True{} : Bool}, +hn: {Nat.is_lt(0n, SS.len(V)) == True{} : Bool}) -> {ArT.big.val(ArT.med2(ArT.sort(ArT.devs(ArT.sort(ArT.shifted(V, ArT.low(base, V), sc)), ArT.med2(ArT.sort(ArT.shifted(V, ArT.low(base, V), sc)), SS.len(V)))), SS.len(V))) == SS.mad4(V, sc) : Nat}:
  +n = SS.len(V)
  +lo = ArT.low(base, V)
  +glo = CO.ac.low_good(K, sc, base, V, gb, gs)
  +ge = CN.ac.and_r(Nat.is_le(CO.ac.o(K, sc, lo), CO.ac.o(K, sc, base)), CO.ac.ge(K, sc, V, CO.ac.o(K, sc, lo)), CO.ac.low_le(K, sc, base, V, gb, gs))
  +c = CO.ac.o(K, sc, lo)
  +S = ArT.shifted(V, lo, sc)
  +U = CS.ac.vals(S)
  +NU = SS.nsort(U)
  +odd = Nat.is_eq(Nat.mod(n, 2n), 1n)
  +h = Nat.div(n, 2n)
  +Mv = SS.nmed2.at(odd, NU, h)
  +hS = ac.shifted_dok(K, sc, lo, V, glo, gs)
  +xs = ArT.sort(S)
  +hxs = CS.ac.sort_dok(S, hS)
  +ex = CS.ac.sort_val(S, hS)
  +M = ArT.med2.at(odd, xs, h)
  +hM = CM.ac.med2_dok(odd, xs, h, hxs)
  +eM = Equal.trans(Nat, ArT.big.val(M), SS.nmed2.at(odd, CS.ac.vals(xs), h), Mv, CM.ac.med2_val(odd, xs, h), Equal.cong(List<&2, Nat>, Nat, l => SS.nmed2.at(odd, l, h), CS.ac.vals(xs), NU, ex))
  +D = ArT.devs(xs, M)
  +hD = CM.ac.devs_dok(xs, M, hxs, hM)
  +eD = {%ex : {CS.ac.vals(D) == CM.ac.dv(_, Mv) : List<&2, Nat>}; %eM : {CS.ac.vals(D) == CM.ac.dv(CS.ac.vals(xs), _) : List<&2, Nat>}; CM.ac.devs_val(xs, M, hxs, hM) : {CS.ac.vals(D) == CM.ac.dv(NU, Mv) : List<&2, Nat>}}
  +ys = ArT.sort(D)
  +eys = Equal.trans(List<&2, Nat>, CS.ac.vals(ys), SS.nsort(CS.ac.vals(D)), SS.nsort(CM.ac.dv(NU, Mv)), CS.ac.sort_val(D, hD), Equal.cong(List<&2, Nat>, List<&2, Nat>, l => SS.nsort(l), CS.ac.vals(D), CM.ac.dv(NU, Mv), eD))
  +zs0 = SS.zs_of(V, sc)
  +zs = SS.zsort(zs0)
  +rz0 = ac.zs_rng(K, sc, V, gs)
  +rz = CS.ac.zsort_rng(K, zs0, rz0)
  +E1 = Equal.trans(List<&2, Nat>, CS.ac.offs(K, zs), SS.nsort(CS.ac.offs(K, zs0)), CS.ac.addc(c, NU), CS.ac.zsort_off(K, zs0, rz0), Equal.trans(List<&2, Nat>, SS.nsort(CS.ac.offs(K, zs0)), SS.nsort(CS.ac.addc(c, U)), CS.ac.addc(c, NU), Equal.cong(List<&2, Nat>, List<&2, Nat>, l => SS.nsort(l), CS.ac.offs(K, zs0), CS.ac.addc(c, U), ac.offs_shift(K, sc, lo, V, glo, gs, ge)), CS.ac.nsort_addc(c, U)))
  +lz = Equal.trans(Nat, CS.ac.zlen(zs), CS.ac.zlen(zs0), n, CS.ac.zsort_len(zs0), ac.zs_len(V, sc))
  +h1 = CM.ac.half(n, hn)
  +h0 = CM.ac.half1(n, hn)
  +b1 = ac.lt_by(h, CS.ac.zlen(zs), n, lz, h1)
  +b0 = ac.lt_by(Nat.sub(h, 1n), CS.ac.zlen(zs), n, lz, h0)
  +nNU = ac.nlen_NU(K, c, NU, zs, n, E1, lz)
  +c1 = ac.lt_by(h, CS.ac.nlen(NU), n, nNU, h1)
  +c0 = ac.lt_by(Nat.sub(h, 1n), CS.ac.nlen(NU), n, nNU, h0)
  +m2 = SS.zmed2.at(odd, zs, h)
  +rm = CM.ac.zmed2_rng(odd, K, zs, h, rz)
  +E2 = Equal.trans(Nat, CZ.ac.off(Nat.add(K, K), m2), SS.nmed2.at(odd, CS.ac.offs(K, zs), h), Nat.add(Nat.add(c, c), Mv), CM.ac.zmed2_off(odd, K, zs, h, rz, b1, b0), Equal.trans(Nat, SS.nmed2.at(odd, CS.ac.offs(K, zs), h), SS.nmed2.at(odd, CS.ac.addc(c, NU), h), Nat.add(Nat.add(c, c), Mv), Equal.cong(List<&2, Nat>, Nat, l => SS.nmed2.at(odd, l, h), CS.ac.offs(K, zs), CS.ac.addc(c, NU), E1), CM.ac.nmed2_addc(odd, c, NU, h, c1, c0)))
  +E3 = {%E2 : {SS.devs2(zs, m2) == CM.ac.dv(CS.ac.addc(c, NU), _) : List<&2, Nat>}; %E1 : {SS.devs2(zs, m2) == CM.ac.dv(_, CZ.ac.off(Nat.add(K, K), m2)) : List<&2, Nat>}; CM.ac.devs2_off(K, zs, m2, rz, rm) : {SS.devs2(zs, m2) == CM.ac.dv(CS.ac.addc(c, NU), Nat.add(Nat.add(c, c), Mv)) : List<&2, Nat>}}
  +E4 = Equal.trans(List<&2, Nat>, SS.devs2(zs, m2), CM.ac.dv(CS.ac.addc(c, NU), Nat.add(Nat.add(c, c), Mv)), CM.ac.dv(NU, Mv), E3, CM.ac.dv_addc(c, NU, Mv))
  %Equal.sym(Nat, ArT.big.val(ArT.med2.at(odd, ys, h)), SS.nmed2.at(odd, CS.ac.vals(ys), h), CM.ac.med2_val(odd, ys, h)) : {_ == SS.mad4(V, sc) : Nat}
  %Equal.sym(List<&2, Nat>, CS.ac.vals(ys), SS.nsort(CM.ac.dv(NU, Mv)), eys) : {SS.nmed2.at(odd, _, h) == SS.mad4(V, sc) : Nat}
  %Equal.sym(List<&2, Nat>, SS.devs2(zs, m2), CM.ac.dv(NU, Mv), E4) : {SS.nmed2.at(odd, SS.nsort(CM.ac.dv(NU, Mv)), h) == SS.nmed2.at(odd, SS.nsort(_), h) : Nat}
  {==}

def ac.mad_dok(+K: Nat, +sc: Nat, +base: ArD.Dec, +V: List<&2, ArD.Dec>, +gb: {CO.ac.good(K, sc, base) == True{} : Bool}, +gs: {CO.ac.allgood(K, sc, V) == True{} : Bool}) -> {SD.digits_ok(ArT.med2(ArT.sort(ArT.devs(ArT.sort(ArT.shifted(V, ArT.low(base, V), sc)), ArT.med2(ArT.sort(ArT.shifted(V, ArT.low(base, V), sc)), SS.len(V)))), SS.len(V))) == True{} : Bool}:
  +n = SS.len(V)
  +lo = ArT.low(base, V)
  +glo = CO.ac.low_good(K, sc, base, V, gb, gs)
  +odd = Nat.is_eq(Nat.mod(n, 2n), 1n)
  +h = Nat.div(n, 2n)
  +S = ArT.shifted(V, lo, sc)
  +xs = ArT.sort(S)
  +hxs = CS.ac.sort_dok(S, ac.shifted_dok(K, sc, lo, V, glo, gs))
  +M = ArT.med2.at(odd, xs, h)
  +D = ArT.devs(xs, M)
  CM.ac.med2_dok(odd, ArT.sort(D), h, CS.ac.sort_dok(D, CM.ac.devs_dok(xs, M, hxs, CM.ac.med2_dok(odd, xs, h, hxs))))
