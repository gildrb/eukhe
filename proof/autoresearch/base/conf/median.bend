# eukhe: medians and deviations of bend/autoresearch/stats.bend (med2,
# devs) and spec/autoresearch/stats.bend (zmed2, nmed2, devs2) for the
# proof of LAW confidence_exact

import Base
import ../../../../bend/autoresearch/dec.bend as ArD
import ../../../../bend/autoresearch/stats.bend as ArT
import ../../../../spec/autoresearch/decimal.bend as SD
import ../../../../spec/autoresearch/stats.bend as SS
import ./nat.bend as CN
import ./big.bend as CB
import ./zint.bend as CZ
import ./sort.bend as CS

# Picking
# -------

def ac.at_val(xs: List<&2, List<&2, Nat>>, i: Nat) -> {ArT.big.val(ArT.at(xs, i)) == SS.nat_at(CS.ac.vals(xs), i) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match i:
        case 0n:
          {==}
        case 1n++j:
          ac.at_val(t, j)

def ac.at_dok(xs: List<&2, List<&2, Nat>>, i: Nat, +h: {CS.ac.adok(xs) == True{} : Bool}) -> {SD.digits_ok(ArT.at(xs, i)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      match i:
        case 0n:
          CS.ac.adok_hd(x, t, h)
        case 1n++j:
          ac.at_dok(t, j, CS.ac.adok_tl(x, t, h))

def ac.zat_off(+K: Nat, zs: List<&2, SS.Z>, i: Nat, +b: {Nat.is_lt(i, CS.ac.zlen(zs)) == True{} : Bool}) -> {CZ.ac.off(K, SS.zat(zs, i)) == SS.nat_at(CS.ac.offs(K, zs), i) : Nat}:
  match zs:
    case Nil{}:
      CN.ac.lt0({CZ.ac.off(K, SS.zat(Nil{}, i)) == SS.nat_at(Nil{}, i) : Nat}, i, b)
    case z <> +t:
      match i:
        case 0n:
          {==}
        case 1n++j:
          ac.zat_off(K, t, j, b)

def ac.zat_rng(+K: Nat, zs: List<&2, SS.Z>, i: Nat, +rs: {CS.ac.arng(K, zs) == True{} : Bool}) -> {CZ.ac.rng(K, SS.zat(zs, i)) == True{} : Bool}:
  match zs:
    case Nil{}:
      {==}
    case +z <> +t:
      match i:
        case 0n:
          CN.ac.and_l(CZ.ac.rng(K, z), CS.ac.arng(K, t), rs)
        case 1n++j:
          ac.zat_rng(K, t, j, CN.ac.and_r(CZ.ac.rng(K, z), CS.ac.arng(K, t), rs))

def ac.nat_at_addc(+c: Nat, ns: List<&2, Nat>, i: Nat, +b: {Nat.is_lt(i, CS.ac.nlen(ns)) == True{} : Bool}) -> {SS.nat_at(CS.ac.addc(c, ns), i) == Nat.add(c, SS.nat_at(ns, i)) : Nat}:
  match ns:
    case Nil{}:
      CN.ac.lt0({SS.nat_at(Nil{}, i) == Nat.add(c, SS.nat_at(Nil{}, i)) : Nat}, i, b)
    case n <> +t:
      match i:
        case 0n:
          {==}
        case 1n++j:
          ac.nat_at_addc(c, t, j, b)

# Medians
# -------

# the code's doubled median is worth the spec's on the values
def ac.med2_val(odd: Bool, +xs: List<&2, List<&2, Nat>>, +h: Nat) -> {ArT.big.val(ArT.med2.at(odd, xs, h)) == SS.nmed2.at(odd, CS.ac.vals(xs), h) : Nat}:
  match odd:
    case True{}:
      +A = ArT.at(xs, h)
      +vA = ArT.big.val(A)
      +V = CS.ac.vals(xs)
      %ac.at_val(xs, h) : {ArT.big.val(ArT.big.add(A, A, 0n)) == Nat.add(_, SS.nat_at(V, h)) : Nat}
      %ac.at_val(xs, h) : {ArT.big.val(ArT.big.add(A, A, 0n)) == Nat.add(vA, _) : Nat}
      %Equal.sym(Nat, ArT.big.val(ArT.big.add(A, A, 0n)), Nat.add(vA, Nat.add(vA, 0n)), CB.ac.val_add(A, A, 0n)) : {_ == Nat.add(vA, vA) : Nat}
      %Equal.sym(Nat, Nat.add(vA, 0n), vA, CN.ac.add_zero(vA)) : {Nat.add(vA, _) == Nat.add(vA, vA) : Nat}
      {==}
    case False{}:
      +A = ArT.at(xs, Nat.sub(h, 1n))
      +B = ArT.at(xs, h)
      +vA = ArT.big.val(A)
      +vB = ArT.big.val(B)
      +V = CS.ac.vals(xs)
      %ac.at_val(xs, Nat.sub(h, 1n)) : {ArT.big.val(ArT.big.add(A, B, 0n)) == Nat.add(_, SS.nat_at(V, h)) : Nat}
      %ac.at_val(xs, h) : {ArT.big.val(ArT.big.add(A, B, 0n)) == Nat.add(vA, _) : Nat}
      %Equal.sym(Nat, ArT.big.val(ArT.big.add(A, B, 0n)), Nat.add(vA, Nat.add(vB, 0n)), CB.ac.val_add(A, B, 0n)) : {_ == Nat.add(vA, vB) : Nat}
      %Equal.sym(Nat, Nat.add(vB, 0n), vB, CN.ac.add_zero(vB)) : {Nat.add(vA, _) == Nat.add(vA, vB) : Nat}
      {==}

def ac.med2_dok(odd: Bool, +xs: List<&2, List<&2, Nat>>, +h: Nat, +hs: {CS.ac.adok(xs) == True{} : Bool}) -> {SD.digits_ok(ArT.med2.at(odd, xs, h)) == True{} : Bool}:
  match odd:
    case True{}:
      +hA = ac.at_dok(xs, h, hs)
      CB.ac.dok_add(ArT.at(xs, h), ArT.at(xs, h), 0n, hA, hA, {==})
    case False{}:
      CB.ac.dok_add(ArT.at(xs, Nat.sub(h, 1n)), ArT.at(xs, h), 0n, ac.at_dok(xs, Nat.sub(h, 1n), hs), ac.at_dok(xs, h, hs), {==})

# the spec's doubled median, shifted by 2K, is the doubled median of the
# shifted integers
def ac.zmed2_off(odd: Bool, +K: Nat, +zs: List<&2, SS.Z>, +h: Nat, +rs: {CS.ac.arng(K, zs) == True{} : Bool}, +b1: {Nat.is_lt(h, CS.ac.zlen(zs)) == True{} : Bool}, +b0: {Nat.is_lt(Nat.sub(h, 1n), CS.ac.zlen(zs)) == True{} : Bool}) -> {CZ.ac.off(Nat.add(K, K), SS.zmed2.at(odd, zs, h)) == SS.nmed2.at(odd, CS.ac.offs(K, zs), h) : Nat}:
  match odd:
    case True{}:
      +a = SS.zat(zs, h)
      +ra = ac.zat_rng(K, zs, h, rs)
      %ac.zat_off(K, zs, h, b1) : {CZ.ac.off(Nat.add(K, K), SS.z_add(a, a)) == Nat.add(_, SS.nat_at(CS.ac.offs(K, zs), h)) : Nat}
      %ac.zat_off(K, zs, h, b1) : {CZ.ac.off(Nat.add(K, K), SS.z_add(a, a)) == Nat.add(CZ.ac.off(K, a), _) : Nat}
      CZ.ac.z_add_off(K, a, a, ra, ra)
    case False{}:
      +a = SS.zat(zs, Nat.sub(h, 1n))
      +b = SS.zat(zs, h)
      %ac.zat_off(K, zs, Nat.sub(h, 1n), b0) : {CZ.ac.off(Nat.add(K, K), SS.z_add(a, b)) == Nat.add(_, SS.nat_at(CS.ac.offs(K, zs), h)) : Nat}
      %ac.zat_off(K, zs, h, b1) : {CZ.ac.off(Nat.add(K, K), SS.z_add(a, b)) == Nat.add(CZ.ac.off(K, a), _) : Nat}
      CZ.ac.z_add_off(K, a, b, ac.zat_rng(K, zs, Nat.sub(h, 1n), rs), ac.zat_rng(K, zs, h, rs))

def ac.zmed2_rng(odd: Bool, +K: Nat, +zs: List<&2, SS.Z>, +h: Nat, +rs: {CS.ac.arng(K, zs) == True{} : Bool}) -> {CZ.ac.rng(Nat.add(K, K), SS.zmed2.at(odd, zs, h)) == True{} : Bool}:
  match odd:
    case True{}:
      +ra = ac.zat_rng(K, zs, h, rs)
      CZ.ac.z_add_rng(K, SS.zat(zs, h), SS.zat(zs, h), ra, ra)
    case False{}:
      CZ.ac.z_add_rng(K, SS.zat(zs, Nat.sub(h, 1n)), SS.zat(zs, h), ac.zat_rng(K, zs, Nat.sub(h, 1n), rs), ac.zat_rng(K, zs, h, rs))

# a doubled median of values shifted by c is shifted by 2c
def ac.nmed2_addc(odd: Bool, +c: Nat, +ns: List<&2, Nat>, +h: Nat, +b1: {Nat.is_lt(h, CS.ac.nlen(ns)) == True{} : Bool}, +b0: {Nat.is_lt(Nat.sub(h, 1n), CS.ac.nlen(ns)) == True{} : Bool}) -> {SS.nmed2.at(odd, CS.ac.addc(c, ns), h) == Nat.add(Nat.add(c, c), SS.nmed2.at(odd, ns, h)) : Nat}:
  match odd:
    case True{}:
      +a = SS.nat_at(ns, h)
      %Equal.sym(Nat, SS.nat_at(CS.ac.addc(c, ns), h), Nat.add(c, SS.nat_at(ns, h)), ac.nat_at_addc(c, ns, h, b1)) : {Nat.add(_, SS.nat_at(CS.ac.addc(c, ns), h)) == Nat.add(Nat.add(c, c), Nat.add(a, a)) : Nat}
      %Equal.sym(Nat, SS.nat_at(CS.ac.addc(c, ns), h), Nat.add(c, SS.nat_at(ns, h)), ac.nat_at_addc(c, ns, h, b1)) : {Nat.add(Nat.add(c, a), _) == Nat.add(Nat.add(c, c), Nat.add(a, a)) : Nat}
      CN.ac.add_4(c, a, c, a)
    case False{}:
      +a = SS.nat_at(ns, Nat.sub(h, 1n))
      +b = SS.nat_at(ns, h)
      %Equal.sym(Nat, SS.nat_at(CS.ac.addc(c, ns), Nat.sub(h, 1n)), Nat.add(c, SS.nat_at(ns, Nat.sub(h, 1n))), ac.nat_at_addc(c, ns, Nat.sub(h, 1n), b0)) : {Nat.add(_, SS.nat_at(CS.ac.addc(c, ns), h)) == Nat.add(Nat.add(c, c), Nat.add(a, b)) : Nat}
      %Equal.sym(Nat, SS.nat_at(CS.ac.addc(c, ns), h), Nat.add(c, SS.nat_at(ns, h)), ac.nat_at_addc(c, ns, h, b1)) : {Nat.add(Nat.add(c, a), _) == Nat.add(Nat.add(c, c), Nat.add(a, b)) : Nat}
      CN.ac.add_4(c, a, c, b)

# Deviations
# ----------

# |2x - m| for each x
def ac.dv(ns: List<&2, Nat>, +m: Nat) -> List<&2, Nat>:
  match ns:
    case Nil{}:
      Nil{}
    case +x <> t:
      CB.ac.dist(Nat.add(x, x), m) <> ac.dv(t, m)

def ac.devs_val(xs: List<&2, List<&2, Nat>>, +M: List<&2, Nat>, +hs: {CS.ac.adok(xs) == True{} : Bool}, +hM: {SD.digits_ok(M) == True{} : Bool}) -> {CS.ac.vals(ArT.devs(xs, M)) == ac.dv(CS.ac.vals(xs), ArT.big.val(M)) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +hx = CS.ac.adok_hd(x, t, hs)
      +vx = ArT.big.val(x)
      +vM = ArT.big.val(M)
      +d = ArT.big.double(x)
      +rest = ac.dv(CS.ac.vals(t), vM)
      %Equal.sym(List<&2, Nat>, CS.ac.vals(ArT.devs(t, M)), rest, ac.devs_val(t, M, CS.ac.adok_tl(x, t, hs), hM)) : {ArT.big.val(ArT.big.diff(d, M)) <> _ == CB.ac.dist(Nat.add(vx, vx), vM) <> rest : List<&2, Nat>}
      %Equal.sym(Nat, ArT.big.val(ArT.big.diff(d, M)), CB.ac.dist(ArT.big.val(d), vM), CB.ac.val_diff(d, M, CB.ac.dok_add(x, x, 0n, hx, hx, {==}), hM)) : {_ <> rest == CB.ac.dist(Nat.add(vx, vx), vM) <> rest : List<&2, Nat>}
      %Equal.sym(Nat, ArT.big.val(d), Nat.add(vx, Nat.add(vx, 0n)), CB.ac.val_add(x, x, 0n)) : {CB.ac.dist(_, vM) <> rest == CB.ac.dist(Nat.add(vx, vx), vM) <> rest : List<&2, Nat>}
      %Equal.sym(Nat, Nat.add(vx, 0n), vx, CN.ac.add_zero(vx)) : {CB.ac.dist(Nat.add(vx, _), vM) <> rest == CB.ac.dist(Nat.add(vx, vx), vM) <> rest : List<&2, Nat>}
      {==}

def ac.devs_dok(xs: List<&2, List<&2, Nat>>, +M: List<&2, Nat>, +hs: {CS.ac.adok(xs) == True{} : Bool}, +hM: {SD.digits_ok(M) == True{} : Bool}) -> {CS.ac.adok(ArT.devs(xs, M)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +t:
      +hx = CS.ac.adok_hd(x, t, hs)
      CN.ac.and_i(SD.digits_ok(ArT.big.diff(ArT.big.double(x), M)), CS.ac.adok(ArT.devs(t, M)), CB.ac.dok_diff(ArT.big.double(x), M, CB.ac.dok_add(x, x, 0n, hx, hx, {==}), hM), ac.devs_dok(t, M, CS.ac.adok_tl(x, t, hs), hM))

def ac.devs2_off(+K: Nat, zs: List<&2, SS.Z>, +m2: SS.Z, +rs: {CS.ac.arng(K, zs) == True{} : Bool}, +rm: {CZ.ac.rng(Nat.add(K, K), m2) == True{} : Bool}) -> {SS.devs2(zs, m2) == ac.dv(CS.ac.offs(K, zs), CZ.ac.off(Nat.add(K, K), m2)) : List<&2, Nat>}:
  match zs:
    case Nil{}:
      {==}
    case +x <> +t:
      +rx = CN.ac.and_l(CZ.ac.rng(K, x), CS.ac.arng(K, t), rs)
      +ox = CZ.ac.off(K, x)
      +om = CZ.ac.off(Nat.add(K, K), m2)
      +xx = SS.z_add(x, x)
      +rest = ac.dv(CS.ac.offs(K, t), om)
      %Equal.sym(List<&2, Nat>, SS.devs2(t, m2), rest, ac.devs2_off(K, t, m2, CN.ac.and_r(CZ.ac.rng(K, x), CS.ac.arng(K, t), rs), rm)) : {SS.z_dist(xx, m2) <> _ == CB.ac.dist(Nat.add(ox, ox), om) <> rest : List<&2, Nat>}
      %Equal.sym(Nat, SS.z_dist(xx, m2), CB.ac.dist(CZ.ac.off(Nat.add(K, K), xx), om), CZ.ac.z_dist_off(Nat.add(K, K), xx, m2, CZ.ac.z_add_rng(K, x, x, rx, rx), rm)) : {_ <> rest == CB.ac.dist(Nat.add(ox, ox), om) <> rest : List<&2, Nat>}
      %Equal.sym(Nat, CZ.ac.off(Nat.add(K, K), xx), Nat.add(ox, ox), CZ.ac.z_add_off(K, x, x, rx, rx)) : {CB.ac.dist(_, om) <> rest == CB.ac.dist(Nat.add(ox, ox), om) <> rest : List<&2, Nat>}
      {==}

def ac.dist_cancel(+C: Nat, +X: Nat, +Y: Nat) -> {CB.ac.dist(Nat.add(C, X), Nat.add(C, Y)) == CB.ac.dist(X, Y) : Nat}:
  %Equal.sym(Nat, Nat.sub(Nat.add(C, X), Nat.add(C, Y)), Nat.sub(X, Y), CN.ac.sub_cancel(C, X, Y)) : {Nat.add(_, Nat.sub(Nat.add(C, Y), Nat.add(C, X))) == CB.ac.dist(X, Y) : Nat}
  %Equal.sym(Nat, Nat.sub(Nat.add(C, Y), Nat.add(C, X)), Nat.sub(Y, X), CN.ac.sub_cancel(C, Y, X)) : {Nat.add(Nat.sub(X, Y), _) == CB.ac.dist(X, Y) : Nat}
  {==}

# deviations of values shifted by c from a median shifted by 2c
def ac.dv_addc(+c: Nat, us: List<&2, Nat>, +Mv: Nat) -> {ac.dv(CS.ac.addc(c, us), Nat.add(Nat.add(c, c), Mv)) == ac.dv(us, Mv) : List<&2, Nat>}:
  match us:
    case Nil{}:
      {==}
    case +u <> +t:
      +rest = ac.dv(t, Mv)
      %Equal.sym(List<&2, Nat>, ac.dv(CS.ac.addc(c, t), Nat.add(Nat.add(c, c), Mv)), rest, ac.dv_addc(c, t, Mv)) : {CB.ac.dist(Nat.add(Nat.add(c, u), Nat.add(c, u)), Nat.add(Nat.add(c, c), Mv)) <> _ == CB.ac.dist(Nat.add(u, u), Mv) <> rest : List<&2, Nat>}
      %Equal.sym(Nat, Nat.add(Nat.add(c, u), Nat.add(c, u)), Nat.add(Nat.add(c, c), Nat.add(u, u)), CN.ac.add_4(c, u, c, u)) : {CB.ac.dist(_, Nat.add(Nat.add(c, c), Mv)) <> rest == CB.ac.dist(Nat.add(u, u), Mv) <> rest : List<&2, Nat>}
      %Equal.sym(Nat, CB.ac.dist(Nat.add(Nat.add(c, c), Nat.add(u, u)), Nat.add(Nat.add(c, c), Mv)), CB.ac.dist(Nat.add(u, u), Mv), ac.dist_cancel(Nat.add(c, c), Nat.add(u, u), Mv)) : {_ <> rest == CB.ac.dist(Nat.add(u, u), Mv) <> rest : List<&2, Nat>}
      {==}

# Halves
# ------

def ac.le_mul2(h: Nat) -> {Nat.is_le(h, Nat.mul(h, 2n)) == True{} : Bool}:
  match h:
    case 0n:
      {==}
    case 1n++p:
      CN.ac.le_trans(p, Nat.mul(p, 2n), 1n+Nat.mul(p, 2n), ac.le_mul2(p), CN.ac.lt_le(Nat.mul(p, 2n), 1n+Nat.mul(p, 2n), CN.ac.lt_succ(Nat.mul(p, 2n))))

def ac.half_at(h: Nat, +r: Nat, -n: Nat, e: {Nat.add(Nat.mul(h, 2n), r) == n : Nat}, +hn: {Nat.is_lt(0n, n) == True{} : Bool}) -> {Nat.is_lt(h, n) == True{} : Bool}:
  match h:
    case 0n:
      hn
    case 1n++p:
      +M = Nat.mul(1n+p, 2n)
      +h1 = {%CN.ac.le_lt_succ(p, Nat.mul(p, 2n)) : {_ == True{} : Bool}; ac.le_mul2(p) : {Nat.is_lt(1n+p, M) == True{} : Bool}}
      +h2 = CN.ac.lt_le_trans(1n+p, M, Nat.add(M, r), h1, CN.ac.le_add(M, r))
      %e : {Nat.is_lt(1n+p, _) == True{} : Bool}
      h2

# half of n > 0 is below n
def ac.half(+n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}) -> {Nat.is_lt(Nat.div(n, 2n), n) == True{} : Bool}:
  ac.half_at(Nat.div(n, 2n), Nat.mod(n, 2n), n, CN.ac.div_eq(n, 1n), hn)

def ac.half1(+n: Nat, +hn: {Nat.is_lt(0n, n) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(Nat.div(n, 2n), 1n), n) == True{} : Bool}:
  CN.ac.le_lt_trans(Nat.sub(Nat.div(n, 2n), 1n), Nat.div(n, 2n), n, CN.ac.sub_le_self(Nat.div(n, 2n), 1n), ac.half(n, hn))
