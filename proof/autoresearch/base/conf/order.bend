# eukhe: the decimal order (bend/autoresearch/dec.bend Dec.cmp) as the
# order of the shifted integers of spec/autoresearch/stats.bend, and the
# smallest metric (stats.bend low), for the proof of LAW confidence_exact

import Base
import ../../../../bend/autoresearch/dec.bend as ArD
import ../../../../bend/autoresearch/stats.bend as ArT
import ../../../../spec/autoresearch/decimal.bend as SD
import ../../../../spec/autoresearch/stats.bend as SS
import ../../../../laws/autoresearch/model.bend as Autoresearch
import ../../metric_order_exact.bend as PArMetricOrderExact
import ./nat.bend as CN
import ./zint.bend as CZ

# a negative sign on a zero magnitude does not move it
def ac.off_neg(+K: Nat, A: Nat, +k: Nat) -> {CZ.ac.off(K, SS.Z{Nat.is_ne(A, 0n), SD.shift(k, A)}) == Nat.sub(K, SD.shift(k, A)) : Nat}:
  match A:
    case 0n:
      %Equal.sym(Nat, SD.shift(k, 0n), 0n, CZ.ac.shift0(k)) : {Nat.add(K, _) == Nat.sub(K, SD.shift(k, 0n)) : Nat}
      %Equal.sym(Nat, SD.shift(k, 0n), 0n, CZ.ac.shift0(k)) : {Nat.add(K, 0n) == Nat.sub(K, _) : Nat}
      Equal.trans(Nat, Nat.add(K, 0n), K, Nat.sub(K, 0n), CN.ac.add_zero(K), Equal.sym(Nat, Nat.sub(K, 0n), K, CN.ac.sub_zero(K)))
    case 1n++a:
      {==}

def ac.rng_neg(+K: Nat, A: Nat, +k: Nat, ra: {CZ.ac.rng(K, SS.Z{Nat.is_ne(A, 0n), SD.shift(k, A)}) == True{} : Bool}) -> {Nat.is_le(SD.shift(k, A), K) == True{} : Bool}:
  match A:
    case 0n:
      %Equal.sym(Nat, SD.shift(k, 0n), 0n, CZ.ac.shift0(k)) : {Nat.is_le(_, K) == True{} : Bool}
      CN.ac.le_zero(K)
    case 1n++a:
      ra

def ac.lt_add_pos(+K: Nat, +Y: Nat, +h: {Nat.is_lt(0n, Y) == True{} : Bool}) -> {Nat.is_lt(K, Nat.add(K, Y)) == True{} : Bool}:
  %CN.ac.add_zero(K) : {Nat.is_lt(_, Nat.add(K, Y)) == True{} : Bool}
  %Equal.sym(Bool, Nat.is_lt(Nat.add(K, 0n), Nat.add(K, Y)), Nat.is_lt(0n, Y), CN.ac.lt_cancel(K, 0n, Y)) : {_ == True{} : Bool}
  h

def ac.sub_pos_lt(K: Nat, X: Nat, h0: {Nat.is_lt(0n, X) == True{} : Bool}, hx: {Nat.is_le(X, K) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(K, X), K) == True{} : Bool}:
  match K X:
    case kk 0n:
      CN.ac.ft({Nat.is_lt(Nat.sub(kk, 0n), kk) == True{} : Bool}, h0)
    case 0n 1n++x:
      CN.ac.ft({Nat.is_lt(Nat.sub(0n, 1n+x), 0n) == True{} : Bool}, hx)
    case 1n++k 1n++x:
      CN.ac.le_lt_trans(Nat.sub(k, x), k, 1n+k, CN.ac.sub_le_self(k, x), CN.ac.lt_succ(k))

# a negative against a positive
def ac.cross_lt(+K: Nat, A: Nat, B: Nat, +p: Nat, +q: Nat, +hx: {Nat.is_le(SD.shift(p, A), K) == True{} : Bool}) -> {SD.order.cross(Bool.and(Nat.is_eq(A, 0n), Nat.is_eq(B, 0n)), LT{}) == Nat.cmp(Nat.sub(K, SD.shift(p, A)), Nat.add(K, SD.shift(q, B))) : Cmp}:
  match A B:
    case 0n 0n:
      %Equal.sym(Nat, SD.shift(p, 0n), 0n, CZ.ac.shift0(p)) : {EQ{} == Nat.cmp(Nat.sub(K, _), Nat.add(K, SD.shift(q, 0n))) : Cmp}
      %Equal.sym(Nat, SD.shift(q, 0n), 0n, CZ.ac.shift0(q)) : {EQ{} == Nat.cmp(Nat.sub(K, 0n), Nat.add(K, _)) : Cmp}
      %Equal.sym(Nat, Nat.sub(K, 0n), K, CN.ac.sub_zero(K)) : {EQ{} == Nat.cmp(_, Nat.add(K, 0n)) : Cmp}
      %Equal.sym(Nat, Nat.add(K, 0n), K, CN.ac.add_zero(K)) : {EQ{} == Nat.cmp(K, _) : Cmp}
      Equal.sym(Cmp, Nat.cmp(K, K), EQ{}, CN.ac.cmp_refl(K))
    case 0n 1n++b:
      +Y = SD.shift(q, 1n+b)
      %Equal.sym(Nat, SD.shift(p, 0n), 0n, CZ.ac.shift0(p)) : {LT{} == Nat.cmp(Nat.sub(K, _), Nat.add(K, Y)) : Cmp}
      %Equal.sym(Nat, Nat.sub(K, 0n), K, CN.ac.sub_zero(K)) : {LT{} == Nat.cmp(_, Nat.add(K, Y)) : Cmp}
      Equal.sym(Cmp, Nat.cmp(K, Nat.add(K, Y)), LT{}, CN.ac.cmp_lt(K, Nat.add(K, Y), ac.lt_add_pos(K, Y, CZ.ac.shift_pos(q, b))))
    case 1n++a bb:
      +X = SD.shift(p, 1n+a)
      +Y = SD.shift(q, bb)
      Equal.sym(Cmp, Nat.cmp(Nat.sub(K, X), Nat.add(K, Y)), LT{}, CN.ac.cmp_lt(Nat.sub(K, X), Nat.add(K, Y), CN.ac.lt_le_trans(Nat.sub(K, X), K, Nat.add(K, Y), ac.sub_pos_lt(K, X, CZ.ac.shift_pos(p, a), hx), CN.ac.le_add(K, Y))))

# a positive against a negative
def ac.cross_gt(+K: Nat, A: Nat, B: Nat, +p: Nat, +q: Nat, +hy: {Nat.is_le(SD.shift(q, B), K) == True{} : Bool}) -> {SD.order.cross(Bool.and(Nat.is_eq(A, 0n), Nat.is_eq(B, 0n)), GT{}) == Nat.cmp(Nat.add(K, SD.shift(p, A)), Nat.sub(K, SD.shift(q, B))) : Cmp}:
  match A B:
    case 0n 0n:
      %Equal.sym(Nat, SD.shift(p, 0n), 0n, CZ.ac.shift0(p)) : {EQ{} == Nat.cmp(Nat.add(K, _), Nat.sub(K, SD.shift(q, 0n))) : Cmp}
      %Equal.sym(Nat, SD.shift(q, 0n), 0n, CZ.ac.shift0(q)) : {EQ{} == Nat.cmp(Nat.add(K, 0n), Nat.sub(K, _)) : Cmp}
      %Equal.sym(Nat, Nat.sub(K, 0n), K, CN.ac.sub_zero(K)) : {EQ{} == Nat.cmp(Nat.add(K, 0n), _) : Cmp}
      %Equal.sym(Nat, Nat.add(K, 0n), K, CN.ac.add_zero(K)) : {EQ{} == Nat.cmp(_, K) : Cmp}
      Equal.sym(Cmp, Nat.cmp(K, K), EQ{}, CN.ac.cmp_refl(K))
    case 0n 1n++b:
      +X = SD.shift(p, 0n)
      +Y = SD.shift(q, 1n+b)
      Equal.sym(Cmp, Nat.cmp(Nat.add(K, X), Nat.sub(K, Y)), GT{}, CN.ac.cmp_gt(Nat.add(K, X), Nat.sub(K, Y), CN.ac.lt_le_trans(Nat.sub(K, Y), K, Nat.add(K, X), ac.sub_pos_lt(K, Y, CZ.ac.shift_pos(q, b), hy), CN.ac.le_add(K, X))))
    case 1n++a bb:
      +X = SD.shift(p, 1n+a)
      +Y = SD.shift(q, bb)
      Equal.sym(Cmp, Nat.cmp(Nat.add(K, X), Nat.sub(K, Y)), GT{}, CN.ac.cmp_gt(Nat.add(K, X), Nat.sub(K, Y), CN.ac.le_lt_trans(Nat.sub(K, Y), K, Nat.add(K, X), CN.ac.sub_le_self(K, Y), ac.lt_add_pos(K, X, CZ.ac.shift_pos(p, a)))))

# the order of two decimals at a scale is that of their shifted integers
def ac.ord_off(a: ArD.Dec, b: ArD.Dec, +sc: Nat, +K: Nat, +la: {Nat.is_le(ArT.scale(a), sc) == True{} : Bool}, +lb: {Nat.is_le(ArT.scale(b), sc) == True{} : Bool}, +ra: {CZ.ac.rng(K, SS.z(a, sc)) == True{} : Bool}, +rb: {CZ.ac.rng(K, SS.z(b, sc)) == True{} : Bool}) -> {SD.order(a, b) == Nat.cmp(CZ.ac.off(K, SS.z(a, sc)), CZ.ac.off(K, SS.z(b, sc))) : Cmp}:
  match a b:
    case ArD.Dec{False{}, +da, +sa} ArD.Dec{False{}, +db, +sb}:
      +A = SD.num(da)
      +B = SD.num(db)
      +X = SD.shift(Nat.sub(sc, sa), A)
      +Y = SD.shift(Nat.sub(sc, sb), B)
      Equal.trans(Cmp, Nat.cmp(SD.shift(sb, A), SD.shift(sa, B)), Nat.cmp(X, Y), Nat.cmp(Nat.add(K, X), Nat.add(K, Y)), CZ.ac.scale_cmp(sa, sb, sc, A, B, la, lb), Equal.sym(Cmp, Nat.cmp(Nat.add(K, X), Nat.add(K, Y)), Nat.cmp(X, Y), CN.ac.cmp_cancel(K, X, Y)))
    case ArD.Dec{True{}, +da, +sa} ArD.Dec{True{}, +db, +sb}:
      +A = SD.num(da)
      +B = SD.num(db)
      +p = Nat.sub(sc, sa)
      +q = Nat.sub(sc, sb)
      +X = SD.shift(p, A)
      +Y = SD.shift(q, B)
      %Equal.sym(Nat, CZ.ac.off(K, SS.Z{Nat.is_ne(A, 0n), X}), Nat.sub(K, X), ac.off_neg(K, A, p)) : {Nat.cmp(SD.shift(sa, B), SD.shift(sb, A)) == Nat.cmp(_, CZ.ac.off(K, SS.Z{Nat.is_ne(B, 0n), Y})) : Cmp}
      %Equal.sym(Nat, CZ.ac.off(K, SS.Z{Nat.is_ne(B, 0n), Y}), Nat.sub(K, Y), ac.off_neg(K, B, q)) : {Nat.cmp(SD.shift(sa, B), SD.shift(sb, A)) == Nat.cmp(Nat.sub(K, X), _) : Cmp}
      Equal.trans(Cmp, Nat.cmp(SD.shift(sa, B), SD.shift(sb, A)), Nat.cmp(Y, X), Nat.cmp(Nat.sub(K, X), Nat.sub(K, Y)), CZ.ac.scale_cmp(sb, sa, sc, B, A, lb, la), Equal.sym(Cmp, Nat.cmp(Nat.sub(K, X), Nat.sub(K, Y)), Nat.cmp(Y, X), CZ.ac.cmp_ss(K, X, Y, ac.rng_neg(K, A, p, ra), ac.rng_neg(K, B, q, rb))))
    case ArD.Dec{True{}, +da, +sa} ArD.Dec{False{}, +db, +sb}:
      +A = SD.num(da)
      +p = Nat.sub(sc, sa)
      %Equal.sym(Nat, CZ.ac.off(K, SS.Z{Nat.is_ne(A, 0n), SD.shift(p, A)}), Nat.sub(K, SD.shift(p, A)), ac.off_neg(K, A, p)) : {SD.order.cross(Bool.and(SD.zero(da), SD.zero(db)), LT{}) == Nat.cmp(_, Nat.add(K, SD.shift(Nat.sub(sc, sb), SD.num(db)))) : Cmp}
      ac.cross_lt(K, A, SD.num(db), p, Nat.sub(sc, sb), ac.rng_neg(K, A, p, ra))
    case ArD.Dec{False{}, +da, +sa} ArD.Dec{True{}, +db, +sb}:
      +B = SD.num(db)
      +q = Nat.sub(sc, sb)
      %Equal.sym(Nat, CZ.ac.off(K, SS.Z{Nat.is_ne(B, 0n), SD.shift(q, B)}), Nat.sub(K, SD.shift(q, B)), ac.off_neg(K, B, q)) : {SD.order.cross(Bool.and(SD.zero(da), SD.zero(db)), GT{}) == Nat.cmp(Nat.add(K, SD.shift(Nat.sub(sc, sa), SD.num(da))), _) : Cmp}
      ac.cross_gt(K, SD.num(da), B, Nat.sub(sc, sa), q, ac.rng_neg(K, B, q, rb))

# Dec.cmp is the order of the shifted integers
def ac.dcmp(+a: ArD.Dec, +b: ArD.Dec, +sc: Nat, +K: Nat, +wa: {SD.Wf(a) == True{} : Bool}, +wb: {SD.Wf(b) == True{} : Bool}, +la: {Nat.is_le(ArT.scale(a), sc) == True{} : Bool}, +lb: {Nat.is_le(ArT.scale(b), sc) == True{} : Bool}, +ra: {CZ.ac.rng(K, SS.z(a, sc)) == True{} : Bool}, +rb: {CZ.ac.rng(K, SS.z(b, sc)) == True{} : Bool}) -> {ArD.Dec.cmp(a, b) == Nat.cmp(CZ.ac.off(K, SS.z(a, sc)), CZ.ac.off(K, SS.z(b, sc))) : Cmp}:
  Equal.trans(Cmp, ArD.Dec.cmp(a, b), SD.order(a, b), Nat.cmp(CZ.ac.off(K, SS.z(a, sc)), CZ.ac.off(K, SS.z(b, sc))), Autoresearch.metric_order_exact(a, b, wa, wb), ac.ord_off(a, b, sc, K, la, lb, ra, rb))

# The smallest metric
# -------------------

# a decimal's shifted integer at scale sc
def ac.o(+K: Nat, +sc: Nat, d: ArD.Dec) -> Nat:
  CZ.ac.off(K, SS.z(d, sc))

# well formed, at most the scale, at least -K
def ac.good(+K: Nat, +sc: Nat, +d: ArD.Dec) -> Bool:
  Bool.and(SD.Wf(d), Bool.and(Nat.is_le(ArT.scale(d), sc), CZ.ac.rng(K, SS.z(d, sc))))

def ac.allgood(+K: Nat, +sc: Nat, vs: List<&2, ArD.Dec>) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case v <> t:
      Bool.and(ac.good(K, sc, v), ac.allgood(K, sc, t))

# every v of vs is at least c
def ac.ge(+K: Nat, +sc: Nat, vs: List<&2, ArD.Dec>, +c: Nat) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case v <> t:
      Bool.and(Nat.is_le(c, ac.o(K, sc, v)), ac.ge(K, sc, t, c))

def ac.g_wf(+K: Nat, +sc: Nat, +d: ArD.Dec, +h: {ac.good(K, sc, d) == True{} : Bool}) -> {SD.Wf(d) == True{} : Bool}:
  CN.ac.and_l(SD.Wf(d), Bool.and(Nat.is_le(ArT.scale(d), sc), CZ.ac.rng(K, SS.z(d, sc))), h)

def ac.g_sc(+K: Nat, +sc: Nat, +d: ArD.Dec, +h: {ac.good(K, sc, d) == True{} : Bool}) -> {Nat.is_le(ArT.scale(d), sc) == True{} : Bool}:
  CN.ac.and_l(Nat.is_le(ArT.scale(d), sc), CZ.ac.rng(K, SS.z(d, sc)), CN.ac.and_r(SD.Wf(d), Bool.and(Nat.is_le(ArT.scale(d), sc), CZ.ac.rng(K, SS.z(d, sc))), h))

def ac.g_rng(+K: Nat, +sc: Nat, +d: ArD.Dec, +h: {ac.good(K, sc, d) == True{} : Bool}) -> {CZ.ac.rng(K, SS.z(d, sc)) == True{} : Bool}:
  CN.ac.and_r(Nat.is_le(ArT.scale(d), sc), CZ.ac.rng(K, SS.z(d, sc)), CN.ac.and_r(SD.Wf(d), Bool.and(Nat.is_le(ArT.scale(d), sc), CZ.ac.rng(K, SS.z(d, sc))), h))

# Dec.cmp of good decimals is the order of their shifted integers
def ac.gcmp(+K: Nat, +sc: Nat, +a: ArD.Dec, +b: ArD.Dec, +ga: {ac.good(K, sc, a) == True{} : Bool}, +gb: {ac.good(K, sc, b) == True{} : Bool}) -> {ArD.Dec.cmp(a, b) == Nat.cmp(ac.o(K, sc, a), ac.o(K, sc, b)) : Cmp}:
  ac.dcmp(a, b, sc, K, ac.g_wf(K, sc, a, ga), ac.g_wf(K, sc, b, gb), ac.g_sc(K, sc, a, ga), ac.g_sc(K, sc, b, gb), ac.g_rng(K, sc, a, ga), ac.g_rng(K, sc, b, gb))

# a lower bound of every v stays one below a smaller c
def ac.ge_mono(+K: Nat, +sc: Nat, vs: List<&2, ArD.Dec>, +c: Nat, +c2: Nat, +h: {Nat.is_le(c2, c) == True{} : Bool}, +g: {ac.ge(K, sc, vs, c) == True{} : Bool}) -> {ac.ge(K, sc, vs, c2) == True{} : Bool}:
  match vs:
    case Nil{}:
      {==}
    case +v <> +t:
      CN.ac.and_i(Nat.is_le(c2, ac.o(K, sc, v)), ac.ge(K, sc, t, c2), CN.ac.le_trans(c2, c, ac.o(K, sc, v), h, CN.ac.and_l(Nat.is_le(c, ac.o(K, sc, v)), ac.ge(K, sc, t, c), g)), ac.ge_mono(K, sc, t, c, c2, h, CN.ac.and_r(Nat.is_le(c, ac.o(K, sc, v)), ac.ge(K, sc, t, c), g)))

def ac.low_good.at(less: Bool, +K: Nat, +sc: Nat, +w: ArD.Dec, +m: ArD.Dec, +gw: {ac.good(K, sc, w) == True{} : Bool}, +gm: {ac.good(K, sc, m) == True{} : Bool}) -> {ac.good(K, sc, ArT.low.at(less, w, m)) == True{} : Bool}:
  match less:
    case True{}:
      gw
    case False{}:
      gm

# the smallest of good decimals is good
def ac.low_good(+K: Nat, +sc: Nat, +v: ArD.Dec, vs: List<&2, ArD.Dec>, +gv: {ac.good(K, sc, v) == True{} : Bool}, +gs: {ac.allgood(K, sc, vs) == True{} : Bool}) -> {ac.good(K, sc, ArT.low(v, vs)) == True{} : Bool}:
  match vs:
    case Nil{}:
      gv
    case +w <> +t:
      +m = ArT.low(v, t)
      ac.low_good.at(Cmp.is_lt(ArD.Dec.cmp(w, m)), K, sc, w, m, CN.ac.and_l(ac.good(K, sc, w), ac.allgood(K, sc, t), gs), ac.low_good(K, sc, v, t, gv, CN.ac.and_r(ac.good(K, sc, w), ac.allgood(K, sc, t), gs)))

# the smallest: at most v, at most every one of vs
def ac.LowP(+K: Nat, +sc: Nat, +v: ArD.Dec, vs: List<&2, ArD.Dec>, +l: ArD.Dec) -> Bool:
  Bool.and(Nat.is_le(ac.o(K, sc, l), ac.o(K, sc, v)), ac.ge(K, sc, vs, ac.o(K, sc, l)))

def ac.low_le.at(less: Bool, +K: Nat, +sc: Nat, +v: ArD.Dec, +w: ArD.Dec, +t: List<&2, ArD.Dec>, +m: ArD.Dec, +hl: {Nat.is_lt(ac.o(K, sc, w), ac.o(K, sc, m)) == less : Bool}, +ih: {ac.LowP(K, sc, v, t, m) == True{} : Bool}) -> {ac.LowP(K, sc, v, w <> t, ArT.low.at(less, w, m)) == True{} : Bool}:
  match less:
    case True{}:
      +ow = ac.o(K, sc, w)
      +om = ac.o(K, sc, m)
      +ov = ac.o(K, sc, v)
      +h1 = CN.ac.and_l(Nat.is_le(om, ov), ac.ge(K, sc, t, om), ih)
      +h2 = CN.ac.and_r(Nat.is_le(om, ov), ac.ge(K, sc, t, om), ih)
      +wm = CN.ac.lt_le(ow, om, hl)
      CN.ac.and_i(Nat.is_le(ow, ov), ac.ge(K, sc, w <> t, ow), CN.ac.le_trans(ow, om, ov, wm, h1), CN.ac.and_i(Nat.is_le(ow, ow), ac.ge(K, sc, t, ow), CN.ac.le_refl(ow), ac.ge_mono(K, sc, t, om, ow, wm, h2)))
    case False{}:
      +ow = ac.o(K, sc, w)
      +om = ac.o(K, sc, m)
      +ov = ac.o(K, sc, v)
      +h1 = CN.ac.and_l(Nat.is_le(om, ov), ac.ge(K, sc, t, om), ih)
      +h2 = CN.ac.and_r(Nat.is_le(om, ov), ac.ge(K, sc, t, om), ih)
      CN.ac.and_i(Nat.is_le(om, ov), ac.ge(K, sc, w <> t, om), h1, CN.ac.and_i(Nat.is_le(om, ow), ac.ge(K, sc, t, om), CN.ac.le_of_not_lt(ow, om, hl), h2))

def ac.low_le(+K: Nat, +sc: Nat, +v: ArD.Dec, vs: List<&2, ArD.Dec>, +gv: {ac.good(K, sc, v) == True{} : Bool}, +gs: {ac.allgood(K, sc, vs) == True{} : Bool}) -> {ac.LowP(K, sc, v, vs, ArT.low(v, vs)) == True{} : Bool}:
  match vs:
    case Nil{}:
      CN.ac.and_i(Nat.is_le(ac.o(K, sc, v), ac.o(K, sc, v)), True{}, CN.ac.le_refl(ac.o(K, sc, v)), {==})
    case +w <> +t:
      +m = ArT.low(v, t)
      +gw = CN.ac.and_l(ac.good(K, sc, w), ac.allgood(K, sc, t), gs)
      +gt = CN.ac.and_r(ac.good(K, sc, w), ac.allgood(K, sc, t), gs)
      +gm = ac.low_good(K, sc, v, t, gv, gt)
      +hl = Equal.cong(Cmp, Bool, x => Cmp.is_lt(x), Nat.cmp(ac.o(K, sc, w), ac.o(K, sc, m)), ArD.Dec.cmp(w, m), Equal.sym(Cmp, ArD.Dec.cmp(w, m), Nat.cmp(ac.o(K, sc, w), ac.o(K, sc, m)), ac.gcmp(K, sc, w, m, gw, gm)))
      ac.low_le.at(Cmp.is_lt(ArD.Dec.cmp(w, m)), K, sc, v, w, t, m, hl, ac.low_le(K, sc, v, t, gv, gt))
