# eukhe: the proof of LAW confidence_exact

import Base
import ../../bend/autoresearch/dec.bend as ArD
import ../../bend/autoresearch/state.bend as ArS
import ../../bend/autoresearch/stats.bend as ArT
import ../../spec/autoresearch/decimal.bend as SD
import ../../spec/autoresearch/stats.bend as SS
import ../../laws/autoresearch/model.bend as Autoresearch
import ./metric_order_exact.bend as PArMetricOrderExact
import ./base/conf/nat.bend as CN
import ./base/conf/big.bend as CB
import ./base/conf/div.bend as CD
import ./base/conf/zint.bend as CZ
import ./base/conf/order.bend as CO
import ./base/conf/rows.bend as CR
import ./base/conf/mad.bend as CA

# 4 d, as the code doubles twice
def ac.four(+v: Nat) -> {Nat.mul(v, 4n) == Nat.add(Nat.add(v, Nat.add(v, 0n)), Nat.add(Nat.add(v, Nat.add(v, 0n)), 0n)) : Nat}:
  +P0 = Nat.add(v, 0n)
  +Q = Nat.add(Nat.add(v, P0), 0n)
  %Equal.sym(Nat, Nat.mul(v, 4n), Nat.add(v, Nat.mul(v, 3n)), CN.ac.mul_succ_r(v, 3n)) : {_ == Nat.add(Nat.add(v, P0), Q) : Nat}
  %Equal.sym(Nat, Nat.mul(v, 3n), Nat.add(v, Nat.mul(v, 2n)), CN.ac.mul_succ_r(v, 2n)) : {Nat.add(v, _) == Nat.add(Nat.add(v, P0), Q) : Nat}
  %Equal.sym(Nat, Nat.mul(v, 2n), Nat.add(v, Nat.mul(v, 1n)), CN.ac.mul_succ_r(v, 1n)) : {Nat.add(v, Nat.add(v, _)) == Nat.add(Nat.add(v, P0), Q) : Nat}
  %Equal.sym(Nat, Nat.mul(v, 1n), Nat.add(v, Nat.mul(v, 0n)), CN.ac.mul_succ_r(v, 0n)) : {Nat.add(v, Nat.add(v, Nat.add(v, _))) == Nat.add(Nat.add(v, P0), Q) : Nat}
  %Equal.sym(Nat, Nat.mul(v, 0n), 0n, CN.ac.mul_zero(v)) : {Nat.add(v, Nat.add(v, Nat.add(v, Nat.add(v, _)))) == Nat.add(Nat.add(v, P0), Q) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(v, P0), Q), Nat.add(v, Nat.add(P0, Q)), CN.ac.add_assoc(v, P0, Q)) : {Nat.add(v, Nat.add(v, Nat.add(v, P0))) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(v, 0n), Q), Nat.add(v, Nat.add(0n, Q)), CN.ac.add_assoc(v, 0n, Q)) : {Nat.add(v, Nat.add(v, Nat.add(v, P0))) == Nat.add(v, _) : Nat}
  %Equal.sym(Nat, Q, Nat.add(v, P0), CN.ac.add_zero(Nat.add(v, P0))) : {Nat.add(v, Nat.add(v, Nat.add(v, P0))) == Nat.add(v, Nat.add(v, _)) : Nat}
  {==}

# 40 d, as the code computes it: 10 (2 (2 d))
def ac.forty(+v: Nat) -> {Nat.mul(Nat.add(Nat.add(v, Nat.add(v, 0n)), Nat.add(Nat.add(v, Nat.add(v, 0n)), 0n)), 10n) == Nat.mul(40n, v) : Nat}:
  %CN.ac.mul_comm(v, 40n) : {Nat.mul(Nat.add(Nat.add(v, Nat.add(v, 0n)), Nat.add(Nat.add(v, Nat.add(v, 0n)), 0n)), 10n) == _ : Nat}
  %CN.ac.mul_assoc(v, 4n, 10n) : {Nat.mul(Nat.add(Nat.add(v, Nat.add(v, 0n)), Nat.add(Nat.add(v, Nat.add(v, 0n)), 0n)), 10n) == _ : Nat}
  %Equal.sym(Nat, Nat.mul(v, 4n), Nat.add(Nat.add(v, Nat.add(v, 0n)), Nat.add(Nat.add(v, Nat.add(v, 0n)), 0n)), ac.four(v)) : {Nat.mul(Nat.add(Nat.add(v, Nat.add(v, 0n)), Nat.add(Nat.add(v, Nat.add(v, 0n)), 0n)), 10n) == Nat.mul(_, 10n) : Nat}
  {==}

# the dividend the code builds is 40 d
def ac.val_40(+D: List<&2, Nat>) -> {ArT.big.val(ArD.cat([0n], ArT.big.double(ArT.big.double(D)))) == Nat.mul(40n, ArT.big.val(D)) : Nat}:
  +v = ArT.big.val(D)
  +dD = ArT.big.double(D)
  +W = Nat.add(v, Nat.add(v, 0n))
  +e1 = {%Equal.sym(Nat, ArT.big.val(dD), W, CB.ac.val_add(D, D, 0n)) : {Nat.add(_, Nat.add(ArT.big.val(dD), 0n)) == Nat.add(W, Nat.add(W, 0n)) : Nat}; %Equal.sym(Nat, ArT.big.val(dD), W, CB.ac.val_add(D, D, 0n)) : {Nat.add(W, Nat.add(_, 0n)) == Nat.add(W, Nat.add(W, 0n)) : Nat}; {==} : {Nat.add(ArT.big.val(dD), Nat.add(ArT.big.val(dD), 0n)) == Nat.add(W, Nat.add(W, 0n)) : Nat}}
  +e2 = Equal.trans(Nat, ArT.big.val(ArT.big.double(dD)), Nat.add(ArT.big.val(dD), Nat.add(ArT.big.val(dD), 0n)), Nat.add(W, Nat.add(W, 0n)), CB.ac.val_add(dD, dD, 0n), e1)
  Equal.trans(Nat, Nat.mul(ArT.big.val(ArT.big.double(dD)), 10n), Nat.mul(Nat.add(W, Nat.add(W, 0n)), 10n), Nat.mul(40n, v), Equal.cong(Nat, Nat, t => Nat.mul(t, 10n), ArT.big.val(ArT.big.double(dD)), Nat.add(W, Nat.add(W, 0n)), e2), ac.forty(v))

def ac.pos(x: Nat, h: {Nat.is_eq(x, 0n) == False{} : Bool}) -> {Nat.is_lt(0n, x) == True{} : Bool}:
  match x:
    case 0n:
      CN.ac.tf({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 1n++p:
      {==}

# the confidence once the MAD is known: none at 0, else the capped quotient
def ac.mad_at(zb: Bool, +D: List<&2, Nat>, +MC: List<&2, Nat>, +m4: Nat, +d: Nat, +ez: {Nat.is_eq(m4, 0n) == zb : Bool}, +em: {ArT.big.val(MC) == m4 : Nat}, +ed: {ArT.big.val(D) == d : Nat}, +hD: {SD.digits_ok(D) == True{} : Bool}, +hM: {SD.digits_ok(MC) == True{} : Bool}) -> {ArT.conf.mad(zb, D, MC) == SS.confidence.mad(zb, m4, d) : Maybe<&2, Nat>}:
  match zb:
    case True{}:
      {==}
    case False{}:
      +A = ArD.cat([0n], ArT.big.double(ArT.big.double(D)))
      +hA = CB.ac.dok_cons(0n, ArT.big.double(ArT.big.double(D)), {==}, CB.ac.dok_add(ArT.big.double(D), ArT.big.double(D), 0n, CB.ac.dok_add(D, D, 0n, hD, hD, {==}), CB.ac.dok_add(D, D, 0n, hD, hD, {==}), {==}))
      +hB = ac.pos(ArT.big.val(MC), {%Equal.sym(Nat, ArT.big.val(MC), m4, em) : {Nat.is_eq(_, 0n) == False{} : Bool}; ez : {Nat.is_eq(ArT.big.val(MC), 0n) == False{} : Bool}})
      %Equal.sym(Nat, ArT.div(A, MC), SS.capped(Nat.div(ArT.big.val(A), ArT.big.val(MC))), CD.ac.div_ok(A, MC, hA, hM, hB)) : {Some{_} == Some{SS.capped(Nat.div(Nat.mul(40n, d), m4))} : Maybe<&2, Nat>}
      %Equal.sym(Nat, ArT.big.val(MC), m4, em) : {Some{SS.capped(Nat.div(ArT.big.val(A), _))} == Some{SS.capped(Nat.div(Nat.mul(40n, d), m4))} : Maybe<&2, Nat>}
      %Equal.sym(Nat, ArT.big.val(A), Nat.mul(40n, d), {%ed : {ArT.big.val(A) == Nat.mul(40n, _) : Nat}; ac.val_40(D) : {ArT.big.val(A) == Nat.mul(40n, d) : Nat}}) : {Some{SS.capped(Nat.div(_, m4))} == Some{SS.capped(Nat.div(Nat.mul(40n, d), m4))} : Maybe<&2, Nat>}
      {==}

# the code's confidence of good metrics with a baseline and a best that
# differ
def ac.go_eq(+W: List<&2, ArD.Dec>, +base: ArD.Dec, +best: ArD.Dec, +gb: {CO.ac.good(CR.ac.ksum(W, SS.top(W)), SS.top(W), base) == True{} : Bool}, +gx: {CO.ac.good(CR.ac.ksum(W, SS.top(W)), SS.top(W), best) == True{} : Bool}, +gs: {CO.ac.allgood(CR.ac.ksum(W, SS.top(W)), SS.top(W), W) == True{} : Bool}, +hn: {Nat.is_lt(0n, SS.len(W)) == True{} : Bool}) -> {ArT.conf.go(W, SS.len(W), base, best) == SS.confidence.of(W, base, best) : Maybe<&2, Nat>}:
  +L = SS.len(W)
  +sc = SS.top(W)
  +K = CR.ac.ksum(W, sc)
  +lo = ArT.low(base, W)
  +MC = ArT.med2(ArT.sort(ArT.devs(ArT.sort(ArT.shifted(W, lo, sc)), ArT.med2(ArT.sort(ArT.shifted(W, lo, sc)), L))), L)
  +D = ArT.diff(best, base, sc)
  +m4 = SS.mad4(W, sc)
  +d = SS.z_dist(SS.z(best, sc), SS.z(base, sc))
  +em = CA.ac.mad(K, sc, base, W, gb, gs, hn)
  +hM = CA.ac.mad_dok(K, sc, base, W, gb, gs)
  +wb = CO.ac.g_wf(K, sc, base, gb)
  +wx = CO.ac.g_wf(K, sc, best, gx)
  +ed = CZ.ac.diff_z(best, base, sc, wx, wb)
  +hD = CA.ac.dok_diffd(best, base, sc, wx, wb)
  +e0 = Equal.cong(Nat, Maybe<&2, Nat>, t => ArT.conf.mad(ArT.big.zero(ArT.med2(ArT.sort(ArT.devs(ArT.sort(ArT.shifted(W, lo, t)), ArT.med2(ArT.sort(ArT.shifted(W, lo, t)), L))), L)), ArT.diff(best, base, t), ArT.med2(ArT.sort(ArT.devs(ArT.sort(ArT.shifted(W, lo, t)), ArT.med2(ArT.sort(ArT.shifted(W, lo, t)), L))), L)), ArT.top_scale(W), sc, CR.ac.top_eq(W))
  +ez = Equal.trans(Bool, ArT.big.zero(MC), Nat.is_eq(ArT.big.val(MC), 0n), Nat.is_eq(m4, 0n), CB.ac.zero_val(MC), Equal.cong(Nat, Bool, k => Nat.is_eq(k, 0n), ArT.big.val(MC), m4, em))
  +e1 = {%Equal.sym(Bool, ArT.big.zero(MC), Nat.is_eq(m4, 0n), ez) : {ArT.conf.mad(_, D, MC) == SS.confidence.mad(Nat.is_eq(m4, 0n), m4, d) : Maybe<&2, Nat>}; ac.mad_at(Nat.is_eq(m4, 0n), D, MC, m4, d, {==}, em, ed, hD, hM) : {ArT.conf.mad(ArT.big.zero(MC), D, MC) == SS.confidence.mad(Nat.is_eq(m4, 0n), m4, d) : Maybe<&2, Nat>}}
  Equal.trans(Maybe<&2, Nat>, ArT.conf.go(W, L, base, best), ArT.conf.mad(ArT.big.zero(MC), D, MC), SS.confidence.of(W, base, best), e0, e1)

def ac.same_eq(cc: Cmp, +W: List<&2, ArD.Dec>, +base: ArD.Dec, +best: ArD.Dec, +gb: {CO.ac.good(CR.ac.ksum(W, SS.top(W)), SS.top(W), base) == True{} : Bool}, +gx: {CO.ac.good(CR.ac.ksum(W, SS.top(W)), SS.top(W), best) == True{} : Bool}, +gs: {CO.ac.allgood(CR.ac.ksum(W, SS.top(W)), SS.top(W), W) == True{} : Bool}, +hn: {Nat.is_lt(0n, SS.len(W)) == True{} : Bool}) -> {ArT.conf.same(cc, W, SS.len(W), base, best) == SS.confidence.same(Cmp.is_eq(cc), W, base, best) : Maybe<&2, Nat>}:
  match cc:
    case EQ{}:
      {==}
    case LT{}:
      ac.go_eq(W, base, best, gb, gx, gs, hn)
    case GT{}:
      ac.go_eq(W, base, best, gb, gx, gs, hn)

def ac.pair_eq(b: Maybe<&2, ArD.Dec>, x: Maybe<&2, ArD.Dec>, +W: List<&2, ArD.Dec>, +mb: {CR.ac.mgood(CR.ac.ksum(W, SS.top(W)), SS.top(W), b) == True{} : Bool}, +mx: {CR.ac.mgood(CR.ac.ksum(W, SS.top(W)), SS.top(W), x) == True{} : Bool}, +gs: {CO.ac.allgood(CR.ac.ksum(W, SS.top(W)), SS.top(W), W) == True{} : Bool}, +hn: {Nat.is_lt(0n, SS.len(W)) == True{} : Bool}) -> {ArT.conf.pair(b, x, W, SS.len(W)) == SS.confidence.pair(W, b, x) : Maybe<&2, Nat>}:
  match b x:
    case Some{+base} Some{+best}:
      +K = CR.ac.ksum(W, SS.top(W))
      +sc = SS.top(W)
      %Equal.sym(Cmp, ArD.Dec.cmp(best, base), SD.order(best, base), Autoresearch.metric_order_exact(best, base, CO.ac.g_wf(K, sc, best, mx), CO.ac.g_wf(K, sc, base, mb))) : {ArT.conf.same(_, W, SS.len(W), base, best) == SS.confidence.same(SD.same(best, base), W, base, best) : Maybe<&2, Nat>}
      ac.same_eq(SD.order(best, base), W, base, best, mb, mx, gs, hn)
    case Some{base} None{}:
      {==}
    case None{} Some{best}:
      {==}
    case None{} None{}:
      {==}

def ac.three(L: Nat, h: {Nat.is_le(3n, L) == True{} : Bool}) -> {Nat.is_lt(0n, L) == True{} : Bool}:
  match L:
    case 0n:
      CN.ac.ft({Nat.is_lt(0n, 0n) == True{} : Bool}, h)
    case 1n++p:
      {==}

def ac.count_eq(enough: Bool, +W: List<&2, ArD.Dec>, b: Maybe<&2, ArD.Dec>, x: Maybe<&2, ArD.Dec>, +eh: {Nat.is_le(3n, SS.len(W)) == enough : Bool}, +mb: {CR.ac.mgood(CR.ac.ksum(W, SS.top(W)), SS.top(W), b) == True{} : Bool}, +mx: {CR.ac.mgood(CR.ac.ksum(W, SS.top(W)), SS.top(W), x) == True{} : Bool}, +gs: {CO.ac.allgood(CR.ac.ksum(W, SS.top(W)), SS.top(W), W) == True{} : Bool}) -> {ArT.conf.count(enough, b, x, W, SS.len(W)) == SS.confidence.count(enough, W, b, x) : Maybe<&2, Nat>}:
  match enough:
    case True{}:
      ac.pair_eq(b, x, W, mb, mx, gs, ac.three(SS.len(W), eh))
    case False{}:
      {==}

def Autoresearch.confidence_exact(s, wf):
  match s:
    case ArS.St{c, +seg, mode, +runs, pend}:
      +V = Autoresearch.ar_vals(runs, seg)
      +sc = SS.top(V)
      +K = CR.ac.ksum(V, sc)
      +b = ArS.first(runs, seg)
      +x = ArS.last(runs, seg)
      +gs = CR.ac.mk_good(K, sc, V, CR.ac.vals_wf(runs, seg, wf), CN.ac.le_refl(sc), CN.ac.le_refl(K))
      +mb = CR.ac.first_good(runs, seg, K, sc, gs)
      +mx = CR.ac.last_good(runs, seg, K, sc, gs)
      +e1 = Equal.cong(List<&2, ArD.Dec>, Maybe<&2, Nat>, w => ArT.conf.count(Nat.is_le(3n, ArT.dlen(w)), b, x, w, ArT.dlen(w)), ArT.vals(runs, seg), V, CR.ac.vals_eq(runs, seg))
      +e2 = Equal.cong(Nat, Maybe<&2, Nat>, k => ArT.conf.count(Nat.is_le(3n, k), b, x, V, k), ArT.dlen(V), SS.len(V), CR.ac.dlen_eq(V))
      +e3 = ac.count_eq(Nat.is_le(3n, SS.len(V)), V, b, x, {==}, mb, mx, gs)
      Equal.trans(Maybe<&2, Nat>, ArT.conf.count(Nat.is_le(3n, ArT.dlen(ArT.vals(runs, seg))), b, x, ArT.vals(runs, seg), ArT.dlen(ArT.vals(runs, seg))), ArT.conf.count(Nat.is_le(3n, ArT.dlen(V)), b, x, V, ArT.dlen(V)), SS.confidence(V, b, x), e1, Equal.trans(Maybe<&2, Nat>, ArT.conf.count(Nat.is_le(3n, ArT.dlen(V)), b, x, V, ArT.dlen(V)), ArT.conf.count(Nat.is_le(3n, SS.len(V)), b, x, V, SS.len(V)), SS.confidence(V, b, x), e2, e3))
