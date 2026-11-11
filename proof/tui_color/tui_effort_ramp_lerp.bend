# eukhe: the proof of LAW tui_effort_ramp_lerp
# ramp.go(1 + l, done) holds, at index k <= l, the rung with w = done + 1
# + k rising and l - k falling (rex.go, by induction on k). For the whole
# ramp (done 0, n = 1 + l, K = k + 1, m = l - k, so K + m = n) each
# channel is the spec's weighted floor: rising (a <= b, d = b - a)
# a (m) + b K = a n + K d, so floor(that / n) = a + floor(K d / n);
# falling (d = a - b) a m + b K = b n + m d, so floor(that / n) =
# b + floor(m d / n) (rl.e_up, rl.e_down, rl.div_add_mul).

import Base
import ../../bend/tui_color.bend as TC
import ../../laws/tui_color.bend as TuiColor
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ./base.bend as LA
import ./tui_color_ffi_band.bend as FB

# Arithmetic
# ----------

# a (x + y) = a x + a y
def rl.mul_add_l(+a: Nat, +x: Nat, +y: Nat) -> {Nat.mul(a, Nat.add(x, y)) == Nat.add(Nat.mul(a, x), Nat.mul(a, y)) : Nat}:
  %FB.fb.mul_comm(Nat.add(x, y), a) : {_ == Nat.add(Nat.mul(a, x), Nat.mul(a, y)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(x, y), a), Nat.add(Nat.mul(x, a), Nat.mul(y, a)), LA.pu.mul_add_r(x, y, a)) : {_ == Nat.add(Nat.mul(a, x), Nat.mul(a, y)) : Nat}
  %FB.fb.mul_comm(a, x) : {Nat.add(_, Nat.mul(y, a)) == Nat.add(Nat.mul(a, x), Nat.mul(a, y)) : Nat}
  %FB.fb.mul_comm(a, y) : {Nat.add(Nat.mul(a, x), _) == Nat.add(Nat.mul(a, x), Nat.mul(a, y)) : Nat}
  {==}

# 1 + b + x is not at most b
def rl.not_le_succ(b: Nat, +x: Nat) -> {Nat.is_le(Nat.add(1n+b, x), b) == False{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n++p:
      rl.not_le_succ(p, x)

def rl.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n++p:
      p

def rl.succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  %e : {a == rl.pred(_) : Nat}
  {==}

# k + a = k + b gives a = b
def rl.add_inj(k: Nat, -a: Nat, -b: Nat, e: {Nat.add(k, a) == Nat.add(k, b) : Nat}) -> {a == b : Nat}:
  match k:
    case 0n:
      e
    case 1n++p:
      rl.add_inj(p, a, b, rl.succ_inj(Nat.add(p, a), Nat.add(p, b), e))

# q (1 + b) + r with r <= b fixes q
def rl.qr_unique(q1: Nat, q2: Nat, +r1: Nat, +r2: Nat, +b: Nat, e: {Nat.add(Nat.mul(q1, 1n+b), r1) == Nat.add(Nat.mul(q2, 1n+b), r2) : Nat}, h1: {Nat.is_le(r1, b) == True{} : Bool}, h2: {Nat.is_le(r2, b) == True{} : Bool}) -> {q1 == q2 : Nat}:
  match q1 q2:
    case 0n 0n:
      {==}
    case 0n 1n++p2:
      +e2 = {%LA.pu.add_assoc(1n+b, Nat.mul(p2, 1n+b), r2) : {r1 == _ : Nat}; e : {r1 == Nat.add(1n+b, Nat.add(Nat.mul(p2, 1n+b), r2)) : Nat}}
      +h3 = {%e2 : {Nat.is_le(_, b) == True{} : Bool}; h1 : {Nat.is_le(Nat.add(1n+b, Nat.add(Nat.mul(p2, 1n+b), r2)), b) == True{} : Bool}}
      LLogicLogic.pu.absurd_ft({0n == 1n+p2 : Nat}, {%rl.not_le_succ(b, Nat.add(Nat.mul(p2, 1n+b), r2)) : {_ == True{} : Bool}; h3 : {False{} == True{} : Bool}})
    case 1n++p1 0n:
      +e2 = {%LA.pu.add_assoc(1n+b, Nat.mul(p1, 1n+b), r1) : {_ == r2 : Nat}; e : {Nat.add(1n+b, Nat.add(Nat.mul(p1, 1n+b), r1)) == r2 : Nat}}
      +h3 = {%Equal.sym(Nat, Nat.add(1n+b, Nat.add(Nat.mul(p1, 1n+b), r1)), r2, e2) : {Nat.is_le(_, b) == True{} : Bool}; h2 : {Nat.is_le(Nat.add(1n+b, Nat.add(Nat.mul(p1, 1n+b), r1)), b) == True{} : Bool}}
      LLogicLogic.pu.absurd_ft({1n+p1 == 0n : Nat}, {%rl.not_le_succ(b, Nat.add(Nat.mul(p1, 1n+b), r1)) : {_ == True{} : Bool}; h3 : {False{} == True{} : Bool}})
    case 1n++p1 1n++p2:
      +e2 = {%LA.pu.add_assoc(1n+b, Nat.mul(p1, 1n+b), r1) : {_ == Nat.add(1n+b, Nat.add(Nat.mul(p2, 1n+b), r2)) : Nat}; %LA.pu.add_assoc(1n+b, Nat.mul(p2, 1n+b), r2) : {Nat.add(Nat.add(1n+b, Nat.mul(p1, 1n+b)), r1) == _ : Nat}; e : {Nat.add(1n+b, Nat.add(Nat.mul(p1, 1n+b), r1)) == Nat.add(1n+b, Nat.add(Nat.mul(p2, 1n+b), r2)) : Nat}}
      +e3 = rl.add_inj(1n+b, Nat.add(Nat.mul(p1, 1n+b), r1), Nat.add(Nat.mul(p2, 1n+b), r2), e2)
      %rl.qr_unique(p1, p2, r1, r2, b, e3, h1, h2) : {1n+p1 == 1n+_ : Nat}
      {==}

# n = q (1 + b) + r with r <= b: n / (1 + b) = q
def rl.div_unique(+n: Nat, +b: Nat, +q: Nat, +r: Nat, e: {Nat.add(Nat.mul(q, 1n+b), r) == n : Nat}, h: {Nat.is_le(r, b) == True{} : Bool}) -> {Nat.div(n, 1n+b) == q : Nat}:
  +e2 = Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(n, 1n+b), 1n+b), Nat.mod(n, 1n+b)), n, Nat.add(Nat.mul(q, 1n+b), r), LA.pu.div_eq(n, b), Equal.sym(Nat, Nat.add(Nat.mul(q, 1n+b), r), n, e))
  rl.qr_unique(Nat.div(n, 1n+b), q, Nat.mod(n, 1n+b), r, b, e2, LA.pu.mod_le(n, b), h)

# c n + x = (c + x / n) n + x mod n
def rl.dam_eq(+c: Nat, +x: Nat, +bp: Nat) -> {Nat.add(Nat.mul(Nat.add(c, Nat.div(x, 1n+bp)), 1n+bp), Nat.mod(x, 1n+bp)) == Nat.add(Nat.mul(c, 1n+bp), x) : Nat}:
  +n = {1n+bp : Nat}
  +q = Nat.div(x, n)
  +r = Nat.mod(x, n)
  %LA.pu.div_eq(x, bp) : {Nat.add(Nat.mul(Nat.add(c, q), n), r) == Nat.add(Nat.mul(c, n), _) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(c, q), n), Nat.add(Nat.mul(c, n), Nat.mul(q, n)), LA.pu.mul_add_r(c, q, n)) : {Nat.add(_, r) == Nat.add(Nat.mul(c, n), Nat.add(Nat.mul(q, n), r)) : Nat}
  %LA.pu.add_assoc(Nat.mul(c, n), Nat.mul(q, n), r) : {Nat.add(Nat.add(Nat.mul(c, n), Nat.mul(q, n)), r) == _ : Nat}
  {==}

# (c n + x) / n = c + x / n, for n = 1 + bp
def rl.div_add_mul(+c: Nat, +x: Nat, +bp: Nat) -> {Nat.div(Nat.add(Nat.mul(c, 1n+bp), x), 1n+bp) == Nat.add(c, Nat.div(x, 1n+bp)) : Nat}:
  rl.div_unique(Nat.add(Nat.mul(c, 1n+bp), x), bp, Nat.add(c, Nat.div(x, 1n+bp)), Nat.mod(x, 1n+bp), rl.dam_eq(c, x, bp), LA.pu.mod_le(x, bp))

# a rising channel (a <= b, d = b - a; K = k + 1, m = l - k, n = l + 1):
# a n + K d = a m + b K
def rl.e_up(+a: Nat, +b: Nat, +k: Nat, +l: Nat, +eu: {Nat.is_le(a, b) == True{} : Bool}, +le: {Nat.is_le(k, l) == True{} : Bool})
  -> {Nat.add(Nat.mul(a, 1n+l), Nat.mul(1n+k, Nat.sub(b, a))) == Nat.add(Nat.mul(a, Nat.sub(l, k)), Nat.mul(b, 1n+k)) : Nat}:
  +K = {1n+k : Nat}
  +N = {1n+l : Nat}
  +m = Nat.sub(l, k)
  +d = Nat.sub(b, a)
  +km = Equal.trans(Nat, Nat.add(m, K), Nat.add(K, m), N, LNat.pa.add_comm(m, K), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(k, m), l, LNat.pu.sub_add(k, l, le)))
  %LNat.pu.sub_add(a, b, eu) : {Nat.add(Nat.mul(a, N), Nat.mul(K, d)) == Nat.add(Nat.mul(a, m), Nat.mul(_, K)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(a, d), K), Nat.add(Nat.mul(a, K), Nat.mul(d, K)), LA.pu.mul_add_r(a, d, K)) : {Nat.add(Nat.mul(a, N), Nat.mul(K, d)) == Nat.add(Nat.mul(a, m), _) : Nat}
  %LA.pu.add_assoc(Nat.mul(a, m), Nat.mul(a, K), Nat.mul(d, K)) : {Nat.add(Nat.mul(a, N), Nat.mul(K, d)) == _ : Nat}
  %rl.mul_add_l(a, m, K) : {Nat.add(Nat.mul(a, N), Nat.mul(K, d)) == Nat.add(_, Nat.mul(d, K)) : Nat}
  %Equal.sym(Nat, Nat.add(m, K), N, km) : {Nat.add(Nat.mul(a, N), Nat.mul(K, d)) == Nat.add(Nat.mul(a, _), Nat.mul(d, K)) : Nat}
  %FB.fb.mul_comm(K, d) : {Nat.add(Nat.mul(a, N), Nat.mul(K, d)) == Nat.add(Nat.mul(a, N), _) : Nat}
  {==}

# a falling channel (b < a, d = a - b): b n + m d = a m + b K
def rl.e_down(+a: Nat, +b: Nat, +k: Nat, +l: Nat, +eu: {Nat.is_le(a, b) == False{} : Bool}, +le: {Nat.is_le(k, l) == True{} : Bool})
  -> {Nat.add(Nat.mul(b, 1n+l), Nat.mul(Nat.sub(l, k), Nat.sub(a, b))) == Nat.add(Nat.mul(a, Nat.sub(l, k)), Nat.mul(b, 1n+k)) : Nat}:
  +K = {1n+k : Nat}
  +N = {1n+l : Nat}
  +m = Nat.sub(l, k)
  +d = Nat.sub(a, b)
  +km = Equal.trans(Nat, Nat.add(m, K), Nat.add(K, m), N, LNat.pa.add_comm(m, K), Equal.cong(Nat, Nat, z => 1n+z, Nat.add(k, m), l, LNat.pu.sub_add(k, l, le)))
  +ba = LA.pu.lt_le(b, a, LA.pu.not_le_lt(a, b, eu))
  %LNat.pu.sub_add(b, a, ba) : {Nat.add(Nat.mul(b, N), Nat.mul(m, d)) == Nat.add(Nat.mul(_, m), Nat.mul(b, K)) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(b, d), m), Nat.add(Nat.mul(b, m), Nat.mul(d, m)), LA.pu.mul_add_r(b, d, m)) : {Nat.add(Nat.mul(b, N), Nat.mul(m, d)) == Nat.add(_, Nat.mul(b, K)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(Nat.mul(b, m), Nat.mul(d, m)), Nat.mul(b, K)), Nat.add(Nat.mul(b, m), Nat.add(Nat.mul(d, m), Nat.mul(b, K))), LA.pu.add_assoc(Nat.mul(b, m), Nat.mul(d, m), Nat.mul(b, K))) : {Nat.add(Nat.mul(b, N), Nat.mul(m, d)) == _ : Nat}
  %LNat.pa.add_comm(Nat.mul(b, K), Nat.mul(d, m)) : {Nat.add(Nat.mul(b, N), Nat.mul(m, d)) == Nat.add(Nat.mul(b, m), _) : Nat}
  %LA.pu.add_assoc(Nat.mul(b, m), Nat.mul(b, K), Nat.mul(d, m)) : {Nat.add(Nat.mul(b, N), Nat.mul(m, d)) == _ : Nat}
  %rl.mul_add_l(b, m, K) : {Nat.add(Nat.mul(b, N), Nat.mul(m, d)) == Nat.add(_, Nat.mul(d, m)) : Nat}
  %Equal.sym(Nat, Nat.add(m, K), N, km) : {Nat.add(Nat.mul(b, N), Nat.mul(m, d)) == Nat.add(Nat.mul(b, _), Nat.mul(d, m)) : Nat}
  %FB.fb.mul_comm(m, d) : {Nat.add(Nat.mul(b, N), Nat.mul(m, d)) == Nat.add(Nat.mul(b, N), _) : Nat}
  {==}

# one channel of rung k + 1 of an (l + 1)-rung ramp is the spec's
def rl.chan(u: Bool, +a: Nat, +b: Nat, +k: Nat, +l: Nat, +eu: {Nat.is_le(a, b) == u : Bool}, +le: {Nat.is_le(k, l) == True{} : Bool})
  -> {TC.chan.pick(u, a, b, 1n+k, Nat.sub(l, k), 1n+l) == TuiColor.lerp(a, b, 1n+k, 1n+l) : Nat}:
  match u:
    case True{}:
      +K = {1n+k : Nat}
      +N = {1n+l : Nat}
      +d = Nat.sub(b, a)
      %rl.e_up(a, b, k, l, eu, le) : {Nat.add(a, Nat.div(Nat.mul(K, d), N)) == Nat.div(_, N) : Nat}
      %Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(a, N), Nat.mul(K, d)), N), Nat.add(a, Nat.div(Nat.mul(K, d), N)), rl.div_add_mul(a, Nat.mul(K, d), l)) : {Nat.add(a, Nat.div(Nat.mul(K, d), N)) == _ : Nat}
      {==}
    case False{}:
      +N = {1n+l : Nat}
      +m = Nat.sub(l, k)
      +d = Nat.sub(a, b)
      %rl.e_down(a, b, k, l, eu, le) : {Nat.add(b, Nat.div(Nat.mul(m, d), N)) == Nat.div(_, N) : Nat}
      %Equal.sym(Nat, Nat.div(Nat.add(Nat.mul(b, N), Nat.mul(m, d)), N), Nat.add(b, Nat.div(Nat.mul(m, d), N)), rl.div_add_mul(b, Nat.mul(m, d), l)) : {Nat.add(b, Nat.div(Nat.mul(m, d), N)) == _ : Nat}
      {==}

# rung k + 1 of an (l + 1)-rung ramp is the spec's, channel by channel
def rl.rung(+lo: TC.Px, +hi: TC.Px, +k: Nat, +l: Nat, +le: {Nat.is_le(k, l) == True{} : Bool}) -> {TC.rung(lo, hi, 1n+k, Nat.sub(l, k), 1n+l) == TuiColor.lerp_px(lo, hi, 1n+k, 1n+l) : TC.Px}:
  match lo hi:
    case TC.Px{+lr, +lg, +lb} TC.Px{+hr, +hg, +hb}:
      +K = {1n+k : Nat}
      +N = {1n+l : Nat}
      +m = Nat.sub(l, k)
      %rl.chan(Nat.is_le(lr, hr), lr, hr, k, l, {==}, le) : {TC.Px{TC.chan(lr, hr, K, m, N), TC.chan(lg, hg, K, m, N), TC.chan(lb, hb, K, m, N)} == TC.Px{_, TuiColor.lerp(lg, hg, K, N), TuiColor.lerp(lb, hb, K, N)} : TC.Px}
      %rl.chan(Nat.is_le(lg, hg), lg, hg, k, l, {==}, le) : {TC.Px{TC.chan(lr, hr, K, m, N), TC.chan(lg, hg, K, m, N), TC.chan(lb, hb, K, m, N)} == TC.Px{TC.chan(lr, hr, K, m, N), _, TuiColor.lerp(lb, hb, K, N)} : TC.Px}
      %rl.chan(Nat.is_le(lb, hb), lb, hb, k, l, {==}, le) : {TC.Px{TC.chan(lr, hr, K, m, N), TC.chan(lg, hg, K, m, N), TC.chan(lb, hb, K, m, N)} == TC.Px{TC.chan(lr, hr, K, m, N), TC.chan(lg, hg, K, m, N), _} : TC.Px}
      {==}

# index k (at most l) of the rungs after the first done ones, 1 + l of
# them to go
def rex.go(+k: Nat, +l: Nat, +done: Nat, +lo: TC.Px, +hi: TC.Px, +n: Nat, +le: {Nat.is_le(k, l) == True{} : Bool})
  -> {List.get(&2, TC.Px, TC.ramp.go(1n+l, done, lo, hi, n), k) == Some{TC.rung(lo, hi, 1n+Nat.add(done, k), Nat.sub(l, k), n)} : Maybe<&2, TC.Px>}:
  match k:
    case 0n:
      %Equal.sym(Nat, Nat.add(done, 0n), done, LNat.pa.add_zero(done)) : {List.get(&2, TC.Px, TC.ramp.go(1n+l, done, lo, hi, n), 0n) == Some{TC.rung(lo, hi, 1n+_, Nat.sub(l, 0n), n)} : Maybe<&2, TC.Px>}
      %LNat.pj.sub_zero(l) : {List.get(&2, TC.Px, TC.ramp.go(1n+l, done, lo, hi, n), 0n) == Some{TC.rung(lo, hi, 1n+done, _, n)} : Maybe<&2, TC.Px>}
      {==}
    case 1n+j:
      match l:
        case 0n:
          LLogicLogic.pu.absurd_ft({List.get(&2, TC.Px, TC.ramp.go(1n, done, lo, hi, n), 1n+j) == Some{TC.rung(lo, hi, 1n+Nat.add(done, 1n+j), Nat.sub(0n, 1n+j), n)} : Maybe<&2, TC.Px>}, le)
        case 1n+m:
          %LNat.add_succ_r(done, j) : {List.get(&2, TC.Px, TC.ramp.go(1n+m, 1n+done, lo, hi, n), j) == Some{TC.rung(lo, hi, 1n+_, Nat.sub(m, j), n)} : Maybe<&2, TC.Px>}
          rex.go(j, m, 1n+done, lo, hi, n, le)

def TuiColor.tui_effort_ramp_lerp(lo, hi, n, k, lt):
  match n:
    case 0n:
      LLogicLogic.pu.absurd_ft({List.get(&2, TC.Px, TC.ramp(lo, hi, 0n), k) == Some{TuiColor.lerp_px(lo, hi, 1n+k, 0n)} : Maybe<&2, TC.Px>}, Equal.trans(Bool, False{}, Nat.is_lt(k, 0n), True{}, LNat.pu.lt_zero_f(k), lt))
    case 1n+l:
      +le = LA.pu.le_succ_of_lt(k, 1n+l, lt)
      %rl.rung(lo, hi, k, l, le) : {List.get(&2, TC.Px, TC.ramp(lo, hi, 1n+l), k) == Some{_} : Maybe<&2, TC.Px>}
      rex.go(k, l, 0n, lo, hi, 1n+l, le)
