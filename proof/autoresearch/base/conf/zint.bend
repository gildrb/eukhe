# eukhe: signed integers (spec/autoresearch/stats.bend Z) as naturals
# shifted by a bound K for the proof of LAW confidence_exact: a value
# z >= -K is worth off(K, z) = K + z; order, distance and sums carry over

import Base
import ../../../../bend/autoresearch/dec.bend as ArD
import ../../../../bend/autoresearch/stats.bend as ArT
import ../../../../spec/autoresearch/decimal.bend as SD
import ../../../../spec/autoresearch/stats.bend as SS
import ./nat.bend as CN
import ./big.bend as CB

# K + z
def ac.off(+K: Nat, z: SS.Z) -> Nat:
  match z:
    case SS.Z{n, m}:
      match n:
        case False{}:
          Nat.add(K, m)
        case True{}:
          Nat.sub(K, m)

# z >= -K
def ac.rng(+K: Nat, z: SS.Z) -> Bool:
  match z:
    case SS.Z{n, m}:
      match n:
        case False{}:
          True{}
        case True{}:
          Nat.is_le(m, K)

# K - x against K - y, for x, y <= K
def ac.cmp_ss(K: Nat, x: Nat, y: Nat, hx: {Nat.is_le(x, K) == True{} : Bool}, hy: {Nat.is_le(y, K) == True{} : Bool}) -> {Nat.cmp(Nat.sub(K, x), Nat.sub(K, y)) == Nat.cmp(y, x) : Cmp}:
  match K x y:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n++q:
      CN.ac.ft({Nat.cmp(0n, 0n) == Nat.cmp(1n+q, 0n) : Cmp}, hy)
    case 0n 1n++p y:
      CN.ac.ft({Nat.cmp(0n, Nat.sub(0n, y)) == Nat.cmp(y, 1n+p) : Cmp}, hx)
    case 1n++k 0n 0n:
      CN.ac.cmp_refl(k)
    case 1n++k 0n 1n++q:
      CN.ac.cmp_gt(1n+k, Nat.sub(k, q), CN.ac.le_lt_trans(Nat.sub(k, q), k, 1n+k, CN.ac.sub_le_self(k, q), CN.ac.lt_succ(k)))
    case 1n++k 1n++p 0n:
      CN.ac.cmp_lt(Nat.sub(k, p), 1n+k, CN.ac.le_lt_trans(Nat.sub(k, p), k, 1n+k, CN.ac.sub_le_self(k, p), CN.ac.lt_succ(k)))
    case 1n++k 1n++p 1n++q:
      ac.cmp_ss(k, p, q, hx, hy)

def ac.le_ss(+K: Nat, +x: Nat, +y: Nat, +hx: {Nat.is_le(x, K) == True{} : Bool}, +hy: {Nat.is_le(y, K) == True{} : Bool}) -> {Nat.is_le(Nat.sub(K, x), Nat.sub(K, y)) == Nat.is_le(y, x) : Bool}:
  Equal.cong(Cmp, Bool, c => Cmp.is_le(c), Nat.cmp(Nat.sub(K, x), Nat.sub(K, y)), Nat.cmp(y, x), ac.cmp_ss(K, x, y, hx, hy))

# (K - x) - (K - y) = y - x, for x, y <= K
def ac.sub_ss(K: Nat, x: Nat, y: Nat, hx: {Nat.is_le(x, K) == True{} : Bool}, hy: {Nat.is_le(y, K) == True{} : Bool}) -> {Nat.sub(Nat.sub(K, x), Nat.sub(K, y)) == Nat.sub(y, x) : Nat}:
  match K x y:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n++q:
      CN.ac.ft({Nat.sub(0n, 0n) == Nat.sub(1n+q, 0n) : Nat}, hy)
    case 0n 1n++p y:
      CN.ac.ft({Nat.sub(0n, Nat.sub(0n, y)) == Nat.sub(y, 1n+p) : Nat}, hx)
    case 1n++k 0n 0n:
      CN.ac.sub_self(k)
    case 1n++k 0n 1n++q:
      CN.ac.sub_of_sum(1n+q, Nat.sub(k, q), 1n+k, {%CN.ac.add_sub(q, k, hy) : {1n+Nat.add(q, Nat.sub(k, q)) == 1n+_ : Nat}; {==} : {Nat.add(1n+q, Nat.sub(k, q)) == 1n+k : Nat}})
    case 1n++k 1n++p 0n:
      CN.ac.sub_le(Nat.sub(k, p), 1n+k, CN.ac.le_trans(Nat.sub(k, p), k, 1n+k, CN.ac.sub_le_self(k, p), CN.ac.lt_le(k, 1n+k, CN.ac.lt_succ(k))))
    case 1n++k 1n++p 1n++q:
      ac.sub_ss(k, p, q, hx, hy)

# K <= K - y is y = 0, for y <= K
def ac.le_K_sub(K: Nat, y: Nat, hy: {Nat.is_le(y, K) == True{} : Bool}) -> {Nat.is_le(K, Nat.sub(K, y)) == Nat.is_eq(y, 0n) : Bool}:
  match K y:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      CN.ac.ft({Nat.is_le(0n, Nat.sub(0n, 1n+q)) == Nat.is_eq(1n+q, 0n) : Bool}, hy)
    case 1n++k 0n:
      CN.ac.le_refl(k)
    case 1n++k 1n++q:
      CN.ac.lt_not_le(Nat.sub(k, q), 1n+k, CN.ac.le_lt_trans(Nat.sub(k, q), k, 1n+k, CN.ac.sub_le_self(k, q), CN.ac.lt_succ(k)))

# (K + y) - (K - x) = x + y, for x <= K
def ac.sub_K(+K: Nat, +x: Nat, +y: Nat, +hx: {Nat.is_le(x, K) == True{} : Bool}) -> {Nat.sub(Nat.add(K, y), Nat.sub(K, x)) == Nat.add(x, y) : Nat}:
  +r = Nat.sub(K, x)
  +e = {%CN.ac.add_sub(x, K, hx) : {Nat.add(Nat.add(x, y), r) == Nat.add(_, y) : Nat}; CN.ac.add_rcomm(x, y, r) : {Nat.add(Nat.add(x, y), r) == Nat.add(K, y) : Nat}}
  CN.ac.sub_of_sum(Nat.add(x, y), r, Nat.add(K, y), e)

def ac.lt_K(+K: Nat, +p: Nat) -> {Nat.is_lt(K, Nat.add(K, 1n+p)) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(K, 1n+p), 1n+Nat.add(K, p), CN.ac.add_succ(K, p)) : {Nat.is_lt(K, _) == True{} : Bool}
  %CN.ac.le_lt_succ(K, Nat.add(K, p)) : {_ == True{} : Bool}
  CN.ac.le_add(K, p)

# Order
# -----

def ac.z_le_ft(x: Nat, +y: Nat, +K: Nat, +hy: {Nat.is_le(y, K) == True{} : Bool}) -> {Bool.and(Nat.is_eq(x, 0n), Nat.is_eq(y, 0n)) == Nat.is_le(Nat.add(K, x), Nat.sub(K, y)) : Bool}:
  match x:
    case 0n:
      %Equal.sym(Nat, Nat.add(K, 0n), K, CN.ac.add_zero(K)) : {Nat.is_eq(y, 0n) == Nat.is_le(_, Nat.sub(K, y)) : Bool}
      Equal.sym(Bool, Nat.is_le(K, Nat.sub(K, y)), Nat.is_eq(y, 0n), ac.le_K_sub(K, y, hy))
    case 1n++p:
      Equal.sym(Bool, Nat.is_le(Nat.add(K, 1n+p), Nat.sub(K, y)), False{}, CN.ac.lt_not_le(Nat.sub(K, y), Nat.add(K, 1n+p), CN.ac.le_lt_trans(Nat.sub(K, y), K, Nat.add(K, 1n+p), CN.ac.sub_le_self(K, y), ac.lt_K(K, p))))

# z_le is the order of the shifted values
def ac.z_le_off(+K: Nat, a: SS.Z, b: SS.Z, +ra: {ac.rng(K, a) == True{} : Bool}, +rb: {ac.rng(K, b) == True{} : Bool}) -> {SS.z_le(a, b) == Nat.is_le(ac.off(K, a), ac.off(K, b)) : Bool}:
  match a b:
    case SS.Z{False{}, +x} SS.Z{False{}, +y}:
      Equal.sym(Bool, Nat.is_le(Nat.add(K, x), Nat.add(K, y)), Nat.is_le(x, y), CN.ac.le_cancel(K, x, y))
    case SS.Z{True{}, +x} SS.Z{True{}, +y}:
      Equal.sym(Bool, Nat.is_le(Nat.sub(K, x), Nat.sub(K, y)), Nat.is_le(y, x), ac.le_ss(K, x, y, ra, rb))
    case SS.Z{True{}, +x} SS.Z{False{}, +y}:
      Equal.sym(Bool, Nat.is_le(Nat.sub(K, x), Nat.add(K, y)), True{}, CN.ac.le_trans(Nat.sub(K, x), K, Nat.add(K, y), CN.ac.sub_le_self(K, x), CN.ac.le_add(K, y)))
    case SS.Z{False{}, +x} SS.Z{True{}, +y}:
      ac.z_le_ft(x, y, K, rb)

# Distance
# --------

# z_dist is the distance of the shifted values
def ac.z_dist_off(+K: Nat, a: SS.Z, b: SS.Z, +ra: {ac.rng(K, a) == True{} : Bool}, +rb: {ac.rng(K, b) == True{} : Bool}) -> {SS.z_dist(a, b) == CB.ac.dist(ac.off(K, a), ac.off(K, b)) : Nat}:
  match a b:
    case SS.Z{False{}, +x} SS.Z{False{}, +y}:
      %Equal.sym(Nat, Nat.sub(Nat.add(K, x), Nat.add(K, y)), Nat.sub(x, y), CN.ac.sub_cancel(K, x, y)) : {Nat.add(Nat.sub(x, y), Nat.sub(y, x)) == Nat.add(_, Nat.sub(Nat.add(K, y), Nat.add(K, x))) : Nat}
      %Equal.sym(Nat, Nat.sub(Nat.add(K, y), Nat.add(K, x)), Nat.sub(y, x), CN.ac.sub_cancel(K, y, x)) : {Nat.add(Nat.sub(x, y), Nat.sub(y, x)) == Nat.add(Nat.sub(x, y), _) : Nat}
      {==}
    case SS.Z{True{}, +x} SS.Z{True{}, +y}:
      %Equal.sym(Nat, Nat.sub(Nat.sub(K, x), Nat.sub(K, y)), Nat.sub(y, x), ac.sub_ss(K, x, y, ra, rb)) : {Nat.add(Nat.sub(x, y), Nat.sub(y, x)) == Nat.add(_, Nat.sub(Nat.sub(K, y), Nat.sub(K, x))) : Nat}
      %Equal.sym(Nat, Nat.sub(Nat.sub(K, y), Nat.sub(K, x)), Nat.sub(x, y), ac.sub_ss(K, y, x, rb, ra)) : {Nat.add(Nat.sub(x, y), Nat.sub(y, x)) == Nat.add(Nat.sub(y, x), _) : Nat}
      CN.ac.add_comm(Nat.sub(x, y), Nat.sub(y, x))
    case SS.Z{True{}, +x} SS.Z{False{}, +y}:
      +z0 = CN.ac.sub_le(Nat.sub(K, x), Nat.add(K, y), CN.ac.le_trans(Nat.sub(K, x), K, Nat.add(K, y), CN.ac.sub_le_self(K, x), CN.ac.le_add(K, y)))
      %Equal.sym(Nat, Nat.sub(Nat.sub(K, x), Nat.add(K, y)), 0n, z0) : {Nat.add(x, y) == Nat.add(_, Nat.sub(Nat.add(K, y), Nat.sub(K, x))) : Nat}
      Equal.sym(Nat, Nat.sub(Nat.add(K, y), Nat.sub(K, x)), Nat.add(x, y), ac.sub_K(K, x, y, ra))
    case SS.Z{False{}, +x} SS.Z{True{}, +y}:
      +z0 = CN.ac.sub_le(Nat.sub(K, y), Nat.add(K, x), CN.ac.le_trans(Nat.sub(K, y), K, Nat.add(K, x), CN.ac.sub_le_self(K, y), CN.ac.le_add(K, x)))
      %Equal.sym(Nat, Nat.sub(Nat.sub(K, y), Nat.add(K, x)), 0n, z0) : {Nat.add(x, y) == Nat.add(Nat.sub(Nat.add(K, x), Nat.sub(K, y)), _) : Nat}
      %Equal.sym(Nat, Nat.sub(Nat.add(K, x), Nat.sub(K, y)), Nat.add(y, x), ac.sub_K(K, y, x, rb)) : {Nat.add(x, y) == Nat.add(_, 0n) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(y, x), 0n), Nat.add(y, x), CN.ac.add_zero(Nat.add(y, x))) : {Nat.add(x, y) == _ : Nat}
      CN.ac.add_comm(x, y)

# Sums
# ----

# x + rx = K
def ac.ksum(+K: Nat, +x: Nat, +hx: {Nat.is_le(x, K) == True{} : Bool}) -> {Nat.add(Nat.sub(K, x), x) == K : Nat}:
  Equal.trans(Nat, Nat.add(Nat.sub(K, x), x), Nat.add(x, Nat.sub(K, x)), K, CN.ac.add_comm(Nat.sub(K, x), x), CN.ac.add_sub(x, K, hx))

# a positive x and a negative y, x < y or not (lt)
def ac.z_add_ft(lt: Bool, +K: Nat, +x: Nat, +y: Nat, +hlt: {Nat.is_lt(x, y) == lt : Bool}, +hy: {Nat.is_le(y, K) == True{} : Bool}) -> {ac.off(Nat.add(K, K), SS.Z{lt, Nat.add(Nat.sub(x, y), Nat.sub(y, x))}) == Nat.add(Nat.add(K, x), Nat.sub(K, y)) : Nat}:
  match lt:
    case True{}:
      +ry = Nat.sub(K, y)
      +T = Nat.add(Nat.add(K, x), ry)
      +hle = CN.ac.lt_le(x, y, hlt)
      +d = Nat.sub(y, x)
      %Equal.sym(Nat, Nat.sub(x, y), 0n, CN.ac.sub_le(x, y, hle)) : {Nat.sub(Nat.add(K, K), Nat.add(_, d)) == T : Nat}
      +e = {%Equal.sym(Nat, Nat.add(Nat.add(Nat.add(K, x), ry), d), Nat.add(Nat.add(K, x), Nat.add(ry, d)), CN.ac.add_assoc(Nat.add(K, x), ry, d)) : {_ == Nat.add(K, K) : Nat}; %Equal.sym(Nat, Nat.add(Nat.add(K, x), Nat.add(ry, d)), Nat.add(K, Nat.add(x, Nat.add(ry, d))), CN.ac.add_assoc(K, x, Nat.add(ry, d))) : {_ == Nat.add(K, K) : Nat}; %CN.ac.add_swap(ry, x, d) : {Nat.add(K, _) == Nat.add(K, K) : Nat}; %Equal.sym(Nat, Nat.add(x, d), y, CN.ac.add_sub(x, y, hle)) : {Nat.add(K, Nat.add(ry, _)) == Nat.add(K, K) : Nat}; %Equal.sym(Nat, Nat.add(ry, y), K, ac.ksum(K, y, hy)) : {Nat.add(K, _) == Nat.add(K, K) : Nat}; {==} : {Nat.add(T, d) == Nat.add(K, K) : Nat}}
      CN.ac.sub_of_sum(T, d, Nat.add(K, K), e)
    case False{}:
      +ry = Nat.sub(K, y)
      +T = Nat.add(Nat.add(K, x), ry)
      +hle = CN.ac.le_of_not_lt(x, y, hlt)
      +e = Nat.sub(x, y)
      %Equal.sym(Nat, Nat.sub(y, x), 0n, CN.ac.sub_le(y, x, hle)) : {Nat.add(Nat.add(K, K), Nat.add(e, _)) == T : Nat}
      %Equal.sym(Nat, Nat.add(e, 0n), e, CN.ac.add_zero(e)) : {Nat.add(Nat.add(K, K), _) == T : Nat}
      %Equal.trans(Nat, Nat.add(ry, y), Nat.add(y, ry), K, CN.ac.add_comm(ry, y), CN.ac.add_sub(y, K, hy)) : {Nat.add(Nat.add(K, _), e) == T : Nat}
      %CN.ac.add_sub(y, x, hle) : {Nat.add(Nat.add(K, Nat.add(ry, y)), e) == Nat.add(Nat.add(K, _), ry) : Nat}
      %CN.ac.add_comm(y, ry) : {Nat.add(Nat.add(K, _), e) == Nat.add(Nat.add(K, Nat.add(y, e)), ry) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(K, Nat.add(y, ry)), e), Nat.add(K, Nat.add(Nat.add(y, ry), e)), CN.ac.add_assoc(K, Nat.add(y, ry), e)) : {_ == Nat.add(Nat.add(K, Nat.add(y, e)), ry) : Nat}
      %Equal.sym(Nat, Nat.add(Nat.add(K, Nat.add(y, e)), ry), Nat.add(K, Nat.add(Nat.add(y, e), ry)), CN.ac.add_assoc(K, Nat.add(y, e), ry)) : {Nat.add(K, Nat.add(Nat.add(y, ry), e)) == _ : Nat}
      %CN.ac.add_rcomm(y, ry, e) : {Nat.add(K, Nat.add(Nat.add(y, ry), e)) == Nat.add(K, _) : Nat}
      {==}

# a sum, shifted by 2K, is the sum of the shifted values
def ac.z_add_off(+K: Nat, a: SS.Z, b: SS.Z, +ra: {ac.rng(K, a) == True{} : Bool}, +rb: {ac.rng(K, b) == True{} : Bool}) -> {ac.off(Nat.add(K, K), SS.z_add(a, b)) == Nat.add(ac.off(K, a), ac.off(K, b)) : Nat}:
  match a b:
    case SS.Z{False{}, +x} SS.Z{False{}, +y}:
      CN.ac.add_4(K, K, x, y)
    case SS.Z{True{}, +x} SS.Z{True{}, +y}:
      +rx = Nat.sub(K, x)
      +ry = Nat.sub(K, y)
      +e = {%Equal.sym(Nat, Nat.add(Nat.add(rx, ry), Nat.add(x, y)), Nat.add(Nat.add(rx, x), Nat.add(ry, y)), CN.ac.add_4(rx, ry, x, y)) : {_ == Nat.add(K, K) : Nat}; %Equal.sym(Nat, Nat.add(rx, x), K, ac.ksum(K, x, ra)) : {Nat.add(_, Nat.add(ry, y)) == Nat.add(K, K) : Nat}; %Equal.sym(Nat, Nat.add(ry, y), K, ac.ksum(K, y, rb)) : {Nat.add(K, _) == Nat.add(K, K) : Nat}; {==} : {Nat.add(Nat.add(rx, ry), Nat.add(x, y)) == Nat.add(K, K) : Nat}}
      CN.ac.sub_of_sum(Nat.add(rx, ry), Nat.add(x, y), Nat.add(K, K), e)
    case SS.Z{False{}, +x} SS.Z{True{}, +y}:
      ac.z_add_ft(Nat.is_lt(x, y), K, x, y, {==}, rb)
    case SS.Z{True{}, +x} SS.Z{False{}, +y}:
      %CN.ac.add_comm(Nat.sub(y, x), Nat.sub(x, y)) : {ac.off(Nat.add(K, K), SS.Z{Nat.is_lt(y, x), _}) == Nat.add(Nat.sub(K, x), Nat.add(K, y)) : Nat}
      %CN.ac.add_comm(Nat.add(K, y), Nat.sub(K, x)) : {ac.off(Nat.add(K, K), SS.Z{Nat.is_lt(y, x), Nat.add(Nat.sub(y, x), Nat.sub(x, y))}) == _ : Nat}
      ac.z_add_ft(Nat.is_lt(y, x), K, y, x, {==}, ra)

def ac.rng_ft(lt: Bool, +K: Nat, +x: Nat, +y: Nat, +hlt: {Nat.is_lt(x, y) == lt : Bool}, +hy: {Nat.is_le(y, K) == True{} : Bool}) -> {ac.rng(Nat.add(K, K), SS.Z{lt, Nat.add(Nat.sub(x, y), Nat.sub(y, x))}) == True{} : Bool}:
  match lt:
    case True{}:
      %Equal.sym(Nat, Nat.sub(x, y), 0n, CN.ac.sub_le(x, y, CN.ac.lt_le(x, y, hlt))) : {Nat.is_le(Nat.add(_, Nat.sub(y, x)), Nat.add(K, K)) == True{} : Bool}
      CN.ac.le_trans(Nat.sub(y, x), K, Nat.add(K, K), CN.ac.le_trans(Nat.sub(y, x), y, K, CN.ac.sub_le_self(y, x), hy), CN.ac.le_add(K, K))
    case False{}:
      {==}

# a sum of values >= -K is >= -2K
def ac.z_add_rng(+K: Nat, a: SS.Z, b: SS.Z, +ra: {ac.rng(K, a) == True{} : Bool}, +rb: {ac.rng(K, b) == True{} : Bool}) -> {ac.rng(Nat.add(K, K), SS.z_add(a, b)) == True{} : Bool}:
  match a b:
    case SS.Z{False{}, +x} SS.Z{False{}, +y}:
      {==}
    case SS.Z{True{}, +x} SS.Z{True{}, +y}:
      CN.ac.le_add_mono(x, K, y, K, ra, rb)
    case SS.Z{False{}, +x} SS.Z{True{}, +y}:
      ac.rng_ft(Nat.is_lt(x, y), K, x, y, {==}, rb)
    case SS.Z{True{}, +x} SS.Z{False{}, +y}:
      %CN.ac.add_comm(Nat.sub(y, x), Nat.sub(x, y)) : {ac.rng(Nat.add(K, K), SS.Z{Nat.is_lt(y, x), _}) == True{} : Bool}
      ac.rng_ft(Nat.is_lt(y, x), K, y, x, {==}, ra)

# Decimals at one scale
# ---------------------

def ac.shift0(k: Nat) -> {SD.shift(k, 0n) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      ac.shift0(j)

def ac.shift_mul(k: Nat, +x: Nat) -> {SD.shift(k, Nat.mul(x, 10n)) == Nat.mul(SD.shift(k, x), 10n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      ac.shift_mul(j, Nat.mul(x, 10n))

def ac.shift_add(j: Nat, +k: Nat, +x: Nat) -> {SD.shift(Nat.add(j, k), x) == SD.shift(j, SD.shift(k, x)) : Nat}:
  match j:
    case 0n:
      {==}
    case 1n++i:
      Equal.trans(Nat, SD.shift(Nat.add(i, k), Nat.mul(x, 10n)), SD.shift(i, SD.shift(k, Nat.mul(x, 10n))), SD.shift(i, Nat.mul(SD.shift(k, x), 10n)), ac.shift_add(i, k, Nat.mul(x, 10n)), Equal.cong(Nat, Nat, t => SD.shift(i, t), SD.shift(k, Nat.mul(x, 10n)), Nat.mul(SD.shift(k, x), 10n), ac.shift_mul(k, x)))

def ac.mul10_cmp(x: Nat, y: Nat) -> {Nat.cmp(Nat.mul(x, 10n), Nat.mul(y, 10n)) == Nat.cmp(x, y) : Cmp}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      {==}
    case 1n++p 0n:
      {==}
    case 1n++p 1n++q:
      ac.mul10_cmp(p, q)

def ac.shift_cmp(k: Nat, +x: Nat, +y: Nat) -> {Nat.cmp(SD.shift(k, x), SD.shift(k, y)) == Nat.cmp(x, y) : Cmp}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      Equal.trans(Cmp, Nat.cmp(SD.shift(j, Nat.mul(x, 10n)), SD.shift(j, Nat.mul(y, 10n))), Nat.cmp(Nat.mul(x, 10n), Nat.mul(y, 10n)), Nat.cmp(x, y), ac.shift_cmp(j, Nat.mul(x, 10n), Nat.mul(y, 10n)), ac.mul10_cmp(x, y))

def ac.shift_pos(k: Nat, +a: Nat) -> {Nat.is_lt(0n, SD.shift(k, 1n+a)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++j:
      ac.shift_pos(j, Nat.add(9n, Nat.mul(a, 10n)))

# a/10^sa against b/10^sb is A 10^(sc-sa) against B 10^(sc-sb)
def ac.scale_cmp(+sa: Nat, +sb: Nat, +sc: Nat, +A: Nat, +B: Nat, +la: {Nat.is_le(sa, sc) == True{} : Bool}, +lb: {Nat.is_le(sb, sc) == True{} : Bool}) -> {Nat.cmp(SD.shift(sb, A), SD.shift(sa, B)) == Nat.cmp(SD.shift(Nat.sub(sc, sa), A), SD.shift(Nat.sub(sc, sb), B)) : Cmp}:
  +p = Nat.sub(sc, sa)
  +q = Nat.sub(sc, sb)
  +m = Nat.add(sa, sb)
  +eA = {%Equal.cong(Nat, Nat, t => Nat.add(t, p), Nat.add(sb, sa), Nat.add(sa, sb), CN.ac.add_comm(sb, sa)) : {_ == Nat.add(sc, sb) : Nat}; %Equal.sym(Nat, Nat.add(Nat.add(sb, sa), p), Nat.add(sb, Nat.add(sa, p)), CN.ac.add_assoc(sb, sa, p)) : {_ == Nat.add(sc, sb) : Nat}; %Equal.sym(Nat, Nat.add(sa, p), sc, CN.ac.add_sub(sa, sc, la)) : {Nat.add(sb, _) == Nat.add(sc, sb) : Nat}; CN.ac.add_comm(sb, sc) : {Nat.add(Nat.add(sa, sb), p) == Nat.add(sc, sb) : Nat}}
  +eB = {%Equal.sym(Nat, Nat.add(Nat.add(sa, sb), q), Nat.add(sa, Nat.add(sb, q)), CN.ac.add_assoc(sa, sb, q)) : {_ == Nat.add(sc, sa) : Nat}; %Equal.sym(Nat, Nat.add(sb, q), sc, CN.ac.add_sub(sb, sc, lb)) : {Nat.add(sa, _) == Nat.add(sc, sa) : Nat}; CN.ac.add_comm(sa, sc) : {Nat.add(Nat.add(sa, sb), q) == Nat.add(sc, sa) : Nat}}
  +rhs = Nat.cmp(SD.shift(p, A), SD.shift(q, B))
  %ac.shift_cmp(sc, SD.shift(sb, A), SD.shift(sa, B)) : {_ == rhs : Cmp}
  %ac.shift_add(sc, sb, A) : {Nat.cmp(_, SD.shift(sc, SD.shift(sa, B))) == rhs : Cmp}
  %ac.shift_add(sc, sa, B) : {Nat.cmp(SD.shift(Nat.add(sc, sb), A), _) == rhs : Cmp}
  %ac.shift_cmp(m, SD.shift(p, A), SD.shift(q, B)) : {Nat.cmp(SD.shift(Nat.add(sc, sb), A), SD.shift(Nat.add(sc, sa), B)) == _ : Cmp}
  %ac.shift_add(m, p, A) : {Nat.cmp(SD.shift(Nat.add(sc, sb), A), SD.shift(Nat.add(sc, sa), B)) == Nat.cmp(_, SD.shift(m, SD.shift(q, B))) : Cmp}
  %ac.shift_add(m, q, B) : {Nat.cmp(SD.shift(Nat.add(sc, sb), A), SD.shift(Nat.add(sc, sa), B)) == Nat.cmp(SD.shift(Nat.add(m, p), A), _) : Cmp}
  %Equal.sym(Nat, Nat.add(m, p), Nat.add(sc, sb), eA) : {Nat.cmp(SD.shift(Nat.add(sc, sb), A), SD.shift(Nat.add(sc, sa), B)) == Nat.cmp(SD.shift(_, A), SD.shift(Nat.add(m, q), B)) : Cmp}
  %Equal.sym(Nat, Nat.add(m, q), Nat.add(sc, sa), eB) : {Nat.cmp(SD.shift(Nat.add(sc, sb), A), SD.shift(Nat.add(sc, sa), B)) == Nat.cmp(SD.shift(Nat.add(sc, sb), A), SD.shift(_, B)) : Cmp}
  {==}

# The decimal difference
# ----------------------

def ac.signs_val(c: Bool, +ma: List<&2, Nat>, +mb: List<&2, Nat>, +ha: {SD.digits_ok(ma) == True{} : Bool}, +hb: {SD.digits_ok(mb) == True{} : Bool}) -> {ArT.big.val(ArT.diff.signs(c, ma, mb)) == SS.z_dist.of(Bool.not(c), ArT.big.val(ma), ArT.big.val(mb)) : Nat}:
  match c:
    case True{}:
      CB.ac.val_diff(ma, mb, ha, hb)
    case False{}:
      %CN.ac.add_zero(ArT.big.val(mb)) : {ArT.big.val(ArT.big.add(ma, mb, 0n)) == Nat.add(ArT.big.val(ma), _) : Nat}
      CB.ac.val_add(ma, mb, 0n)

def ac.of0(b: Bool, +Y: Nat) -> {SS.z_dist.of(b, 0n, Y) == Y : Nat}:
  match b:
    case True{}:
      {==}
    case False{}:
      CN.ac.sub_zero(Y)

def ac.ofy0(b: Bool, +X: Nat) -> {SS.z_dist.of(b, X, 0n) == X : Nat}:
  match b:
    case True{}:
      CN.ac.add_zero(X)
    case False{}:
      Equal.trans(Nat, Nat.add(Nat.sub(X, 0n), 0n), Nat.sub(X, 0n), X, CN.ac.add_zero(Nat.sub(X, 0n)), CN.ac.sub_zero(X))

def ac.of_x0(+b: Bool, +k: Nat, +Y: Nat) -> {SS.z_dist.of(b, SD.shift(k, 0n), Y) == Y : Nat}:
  %Equal.sym(Nat, SD.shift(k, 0n), 0n, ac.shift0(k)) : {SS.z_dist.of(b, _, Y) == Y : Nat}
  ac.of0(b, Y)

def ac.of_y0(+b: Bool, +k: Nat, +X: Nat) -> {SS.z_dist.of(b, X, SD.shift(k, 0n)) == X : Nat}:
  %Equal.sym(Nat, SD.shift(k, 0n), 0n, ac.shift0(k)) : {SS.z_dist.of(b, X, _) == X : Nat}
  ac.ofy0(b, X)

def ac.of_sign_nn(na: Bool, nb: Bool, +X: Nat, +Y: Nat) -> {SS.z_dist.of(Bool.xor(na, nb), X, Y) == SS.z_dist.of(Bool.xor(Bool.and(na, True{}), Bool.and(nb, True{})), X, Y) : Nat}:
  match na nb:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a zero magnitude makes its sign not matter
def ac.of_sign(+na: Bool, +nb: Bool, A: Nat, B: Nat, +k1: Nat, +k2: Nat) -> {SS.z_dist.of(Bool.xor(na, nb), SD.shift(k1, A), SD.shift(k2, B)) == SS.z_dist.of(Bool.xor(Bool.and(na, Nat.is_ne(A, 0n)), Bool.and(nb, Nat.is_ne(B, 0n))), SD.shift(k1, A), SD.shift(k2, B)) : Nat}:
  match A B:
    case 0n +bb:
      +Y = SD.shift(k2, bb)
      +b2 = Bool.xor(Bool.and(na, Nat.is_ne(0n, 0n)), Bool.and(nb, Nat.is_ne(bb, 0n)))
      Equal.trans(Nat, SS.z_dist.of(Bool.xor(na, nb), SD.shift(k1, 0n), Y), Y, SS.z_dist.of(b2, SD.shift(k1, 0n), Y), ac.of_x0(Bool.xor(na, nb), k1, Y), Equal.sym(Nat, SS.z_dist.of(b2, SD.shift(k1, 0n), Y), Y, ac.of_x0(b2, k1, Y)))
    case 1n++a 0n:
      +X = SD.shift(k1, 1n+a)
      +b2 = Bool.xor(Bool.and(na, Nat.is_ne(1n+a, 0n)), Bool.and(nb, Nat.is_ne(0n, 0n)))
      Equal.trans(Nat, SS.z_dist.of(Bool.xor(na, nb), X, SD.shift(k2, 0n)), X, SS.z_dist.of(b2, X, SD.shift(k2, 0n)), ac.of_y0(Bool.xor(na, nb), k2, X), Equal.sym(Nat, SS.z_dist.of(b2, X, SD.shift(k2, 0n)), X, ac.of_y0(b2, k2, X)))
    case 1n++a 1n++b:
      ac.of_sign_nn(na, nb, SD.shift(k1, 1n+a), SD.shift(k2, 1n+b))

def ac.not_not(b: Bool) -> {Bool.not(Bool.not(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's |a - b| at scale sc is the spec's
def ac.diff_z(a: ArD.Dec, b: ArD.Dec, +sc: Nat, +wa: {SD.Wf(a) == True{} : Bool}, +wb: {SD.Wf(b) == True{} : Bool}) -> {ArT.big.val(ArT.diff(a, b, sc)) == SS.z_dist(SS.z(a, sc), SS.z(b, sc)) : Nat}:
  match a b:
    case ArD.Dec{+na, +da, +sa} ArD.Dec{+nb, +db, +sb}:
      +ma = ArT.mag(ArD.Dec{na, da, sa}, sc)
      +mb = ArT.mag(ArD.Dec{nb, db, sb}, sc)
      +A = SD.num(da)
      +B = SD.num(db)
      +k1 = Nat.sub(sc, sa)
      +k2 = Nat.sub(sc, sb)
      +c = Bool.not(Bool.xor(na, nb))
      +rhs = SS.z_dist.of(Bool.xor(Bool.and(na, Nat.is_ne(A, 0n)), Bool.and(nb, Nat.is_ne(B, 0n))), SD.shift(k1, A), SD.shift(k2, B))
      %Equal.sym(Nat, ArT.big.val(ArT.diff.signs(c, ma, mb)), SS.z_dist.of(Bool.not(c), ArT.big.val(ma), ArT.big.val(mb)), ac.signs_val(c, ma, mb, CB.ac.dok_mag(ArD.Dec{na, da, sa}, sc, wa), CB.ac.dok_mag(ArD.Dec{nb, db, sb}, sc, wb))) : {_ == rhs : Nat}
      %Equal.sym(Nat, ArT.big.val(ma), SD.shift(k1, A), CB.ac.val_mag(ArD.Dec{na, da, sa}, sc)) : {SS.z_dist.of(Bool.not(c), _, ArT.big.val(mb)) == rhs : Nat}
      %Equal.sym(Nat, ArT.big.val(mb), SD.shift(k2, B), CB.ac.val_mag(ArD.Dec{nb, db, sb}, sc)) : {SS.z_dist.of(Bool.not(c), SD.shift(k1, A), _) == rhs : Nat}
      %Equal.sym(Bool, Bool.not(c), Bool.xor(na, nb), ac.not_not(Bool.xor(na, nb))) : {SS.z_dist.of(_, SD.shift(k1, A), SD.shift(k2, B)) == rhs : Nat}
      ac.of_sign(na, nb, A, B, k1, k2)
