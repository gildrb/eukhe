# eukhe: the proof of LAW color_lum_weights: the luminance of a color is
# the sum of its three weighted products' values (lrs.sum, from LAW
# color_lum_rises), so 10000 times it is the sum of 10000 times each
# (cw.mul_add_r). Each weighted product k·lin(c) is the product of the
# values K·n (lrs.mul, the leaves' product facts), so the gray of c has
# luminance (K1 + K2 + K3)·n = 10000·n (clw.gray), and (K·n)·10000 =
# (10000·n)·K is Nat algebra (clw.swap): no closed check of its own.
# The weights meet their literals by rewriting (clw.ten, clw.k1-k3), each
# closed check comparing at most 3576 successors: the checker compares
# naturals one successor per stack frame, and comparing K1 + K2 + K3 with
# 10000n in one step came near bend's 5 MB checker stack.

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color
import ./base/lum.bend as LCl
import ./color_lum_rises.bend as PColorLumRises
import ./color_contrast_exact_wide/nat.bend as LCw
import ../base/nat.bend as LNat

# Products commute
# ----------------

def clw.mul_zero_r(n: Nat) -> {Nat.mul(n, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      clw.mul_zero_r(p)

def clw.mul_comm(+a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, clw.mul_zero_r(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), LNat.wn_mul_succ_r(b, p)) : {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      %clw.mul_comm(p, b) : {Nat.add(b, Nat.mul(p, b)) == Nat.add(b, _) : Nat}
      {==}

# (a·n)·s = s·(a·n) = s·(n·a) = (s·n)·a
def clw.swap(+a: Nat, +n: Nat, +s: Nat) -> {Nat.mul(Nat.mul(a, n), s) == Nat.mul(Nat.mul(s, n), a) : Nat}:
  Equal.trans(Nat, Nat.mul(Nat.mul(a, n), s), Nat.mul(s, Nat.mul(a, n)), Nat.mul(Nat.mul(s, n), a),
    clw.mul_comm(Nat.mul(a, n), s),
    Equal.trans(Nat, Nat.mul(s, Nat.mul(a, n)), Nat.mul(s, Nat.mul(n, a)), Nat.mul(Nat.mul(s, n), a),
      Equal.cong(Nat, Nat, z => Nat.mul(s, z), Nat.mul(a, n), Nat.mul(n, a), clw.mul_comm(a, n)),
      Equal.sym(Nat, Nat.mul(Nat.mul(s, n), a), Nat.mul(s, Nat.mul(n, a)), LCw.cw.mul_assoc(s, n, a))))

# The gray
# --------

# the luminance of the gray of c is (K1 + K2 + K3)·n, n the value of lin(c)
def clw.gray(+c: U32) -> {U32.to_nat(Co.lum(Co.Rgb{c, c, c})) == Nat.mul(Nat.add(Nat.add(U32.to_nat(2126), U32.to_nat(7152)), U32.to_nat(722)), U32.to_nat(Co.lin(c))) : Nat}:
  +n = U32.to_nat(Co.lin(c))
  +k1 = U32.to_nat(2126)
  +k2 = U32.to_nat(7152)
  +k3 = U32.to_nat(722)
  +t1 = U32.to_nat((2126 * Co.lin(c) : U32))
  +t2 = U32.to_nat((7152 * Co.lin(c) : U32))
  +t3 = U32.to_nat((722 * Co.lin(c) : U32))
  +s = Nat.mul(Nat.add(Nat.add(k1, k2), k3), n)
  +h = PColorLumRises.lrs.term(c)
  %Equal.sym(Nat, U32.to_nat(Co.lum(Co.Rgb{c, c, c})), Nat.add(Nat.add(t1, t2), t3), PColorLumRises.lrs.sum(c, c, c)) : {_ == s : Nat}
  %Equal.sym(Nat, t1, Nat.mul(k1, n), PColorLumRises.lrs.mul(2126, 21260000, Co.lin(c), PColorLumRises.lrs.m1(Co.lin(c), h))) : {Nat.add(Nat.add(_, t2), t3) == s : Nat}
  %Equal.sym(Nat, t2, Nat.mul(k2, n), PColorLumRises.lrs.mul(7152, 71520000, Co.lin(c), PColorLumRises.lrs.m2(Co.lin(c), h))) : {Nat.add(Nat.add(Nat.mul(k1, n), _), t3) == s : Nat}
  %Equal.sym(Nat, t3, Nat.mul(k3, n), PColorLumRises.lrs.mul(722, 7220000, Co.lin(c), PColorLumRises.lrs.m3(Co.lin(c), h))) : {Nat.add(Nat.add(Nat.mul(k1, n), Nat.mul(k2, n)), _) == s : Nat}
  %LCw.cw.mul_add_r(k1, k2, n) : {Nat.add(_, Nat.mul(k3, n)) == s : Nat}
  Equal.sym(Nat, s, Nat.add(Nat.mul(Nat.add(k1, k2), n), Nat.mul(k3, n)), LCw.cw.mul_add_r(Nat.add(k1, k2), k3, n))

# 10000 times a weighted product k·lin(c) is its weight times the luminance
# of the gray of c (10000 = K1 + K2 + K3)
def clw.w(+k: U32, +m: U32, +c: U32, h: {LCl.cl.mterm(k, m, Co.lin(c)) == True{} : Bool}) -> {Nat.mul(U32.to_nat((k * Co.lin(c) : U32)), Nat.add(Nat.add(U32.to_nat(2126), U32.to_nat(7152)), U32.to_nat(722))) == Nat.mul(U32.to_nat(Co.lum(Co.Rgb{c, c, c})), U32.to_nat(k)) : Nat}:
  +n = U32.to_nat(Co.lin(c))
  +kk = U32.to_nat(k)
  +s = Nat.add(Nat.add(U32.to_nat(2126), U32.to_nat(7152)), U32.to_nat(722))
  +g = U32.to_nat(Co.lum(Co.Rgb{c, c, c}))
  %Equal.sym(Nat, U32.to_nat((k * Co.lin(c) : U32)), Nat.mul(kk, n), PColorLumRises.lrs.mul(k, m, Co.lin(c), h)) : {Nat.mul(_, s) == Nat.mul(g, kk) : Nat}
  %Equal.sym(Nat, g, Nat.mul(s, n), clw.gray(c)) : {Nat.mul(Nat.mul(kk, n), s) == Nat.mul(_, kk) : Nat}
  clw.swap(kk, n, s)

# The weights' literals
# ---------------------

# each closed check below compares at most 3576 successors
def clw.k1() -> {U32.to_nat(2126) == 2126n : Nat}:
  {==}

def clw.k3() -> {U32.to_nat(722) == 722n : Nat}:
  {==}

def clw.k3576() -> {U32.to_nat(3576) == 3576n : Nat}:
  {==}

def clw.p2() -> {(2 * 3576 : U32) == 7152 : U32}:
  {==}

def clw.add0(x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, clw.add0(p))

# 2·x = x + x
def clw.dbl(+x: Nat) -> {Nat.mul(2n, x) == Nat.add(x, x) : Nat}:
  Equal.cong(Nat, Nat, z => Nat.add(x, z), Nat.mul(1n, x), x, clw.add0(x))

# 7152 = 2·3576, a product of values (lrs.mul), and 3576 + 3576 = 7152
def clw.k2() -> {U32.to_nat(7152) == 7152n : Nat}:
  %clw.p2() : {U32.to_nat(_) == 7152n : Nat}
  %Equal.sym(Nat, U32.to_nat((2 * 3576 : U32)), Nat.mul(U32.to_nat(2), U32.to_nat(3576)), PColorLumRises.lrs.mul(2, 7152, 3576, {==})) : {_ == 7152n : Nat}
  %Equal.sym(Nat, U32.to_nat(3576), 3576n, clw.k3576()) : {Nat.mul(U32.to_nat(2), _) == 7152n : Nat}
  %Equal.sym(Nat, U32.to_nat(2), 2n, {==}) : {Nat.mul(_, 3576n) == 7152n : Nat}
  %Equal.sym(Nat, Nat.mul(2n, 3576n), Nat.add(3576n, 3576n), clw.dbl(3576n)) : {_ == 7152n : Nat}
  {==}

# K1 + K2 + K3 = 722 + (2126 + 7152) = 10000
def clw.ten() -> {Nat.add(Nat.add(U32.to_nat(2126), U32.to_nat(7152)), U32.to_nat(722)) == 10000n : Nat}:
  %Equal.sym(Nat, U32.to_nat(2126), 2126n, clw.k1()) : {Nat.add(Nat.add(_, U32.to_nat(7152)), U32.to_nat(722)) == 10000n : Nat}
  %Equal.sym(Nat, U32.to_nat(7152), 7152n, clw.k2()) : {Nat.add(Nat.add(2126n, _), U32.to_nat(722)) == 10000n : Nat}
  %Equal.sym(Nat, U32.to_nat(722), 722n, clw.k3()) : {Nat.add(Nat.add(2126n, 7152n), _) == 10000n : Nat}
  %LNat.add_comm(722n, Nat.add(2126n, 7152n)) : {_ == 10000n : Nat}
  {==}

# 10000 times each weighted product is its weight times the gray's luminance
def clw.red(+c: U32) -> {Nat.mul(U32.to_nat((2126 * Co.lin(c) : U32)), 10000n) == Nat.mul(U32.to_nat(Co.lum(Co.Rgb{c, c, c})), 2126n) : Nat}:
  %clw.ten() : {Nat.mul(U32.to_nat((2126 * Co.lin(c) : U32)), _) == Nat.mul(U32.to_nat(Co.lum(Co.Rgb{c, c, c})), 2126n) : Nat}
  %clw.k1() : {Nat.mul(U32.to_nat((2126 * Co.lin(c) : U32)), Nat.add(Nat.add(U32.to_nat(2126), U32.to_nat(7152)), U32.to_nat(722))) == Nat.mul(U32.to_nat(Co.lum(Co.Rgb{c, c, c})), _) : Nat}
  clw.w(2126, 21260000, c, PColorLumRises.lrs.m1(Co.lin(c), PColorLumRises.lrs.term(c)))

def clw.green(+c: U32) -> {Nat.mul(U32.to_nat((7152 * Co.lin(c) : U32)), 10000n) == Nat.mul(U32.to_nat(Co.lum(Co.Rgb{c, c, c})), 7152n) : Nat}:
  %clw.ten() : {Nat.mul(U32.to_nat((7152 * Co.lin(c) : U32)), _) == Nat.mul(U32.to_nat(Co.lum(Co.Rgb{c, c, c})), 7152n) : Nat}
  %clw.k2() : {Nat.mul(U32.to_nat((7152 * Co.lin(c) : U32)), Nat.add(Nat.add(U32.to_nat(2126), U32.to_nat(7152)), U32.to_nat(722))) == Nat.mul(U32.to_nat(Co.lum(Co.Rgb{c, c, c})), _) : Nat}
  clw.w(7152, 71520000, c, PColorLumRises.lrs.m2(Co.lin(c), PColorLumRises.lrs.term(c)))

def clw.blue(+c: U32) -> {Nat.mul(U32.to_nat((722 * Co.lin(c) : U32)), 10000n) == Nat.mul(U32.to_nat(Co.lum(Co.Rgb{c, c, c})), 722n) : Nat}:
  %clw.ten() : {Nat.mul(U32.to_nat((722 * Co.lin(c) : U32)), _) == Nat.mul(U32.to_nat(Co.lum(Co.Rgb{c, c, c})), 722n) : Nat}
  %clw.k3() : {Nat.mul(U32.to_nat((722 * Co.lin(c) : U32)), Nat.add(Nat.add(U32.to_nat(2126), U32.to_nat(7152)), U32.to_nat(722))) == Nat.mul(U32.to_nat(Co.lum(Co.Rgb{c, c, c})), _) : Nat}
  clw.w(722, 7220000, c, PColorLumRises.lrs.m3(Co.lin(c), PColorLumRises.lrs.term(c)))

# The sum
# -------

def Color.color_lum_weights(r, g, b):
  +t1 = U32.to_nat((2126 * Co.lin(r) : U32))
  +t2 = U32.to_nat((7152 * Co.lin(g) : U32))
  +t3 = U32.to_nat((722 * Co.lin(b) : U32))
  +s1 = Nat.mul(U32.to_nat(Co.lum(Co.Rgb{r, r, r})), 2126n)
  +s2 = Nat.mul(U32.to_nat(Co.lum(Co.Rgb{g, g, g})), 7152n)
  +s3 = Nat.mul(U32.to_nat(Co.lum(Co.Rgb{b, b, b})), 722n)
  %Equal.sym(Nat, U32.to_nat(Co.lum(Co.Rgb{r, g, b})), Nat.add(Nat.add(t1, t2), t3), PColorLumRises.lrs.sum(r, g, b)) : {Nat.mul(_, 10000n) == Nat.add(Nat.add(s1, s2), s3) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(Nat.add(t1, t2), t3), 10000n), Nat.add(Nat.mul(Nat.add(t1, t2), 10000n), Nat.mul(t3, 10000n)), LCw.cw.mul_add_r(Nat.add(t1, t2), t3, 10000n)) : {_ == Nat.add(Nat.add(s1, s2), s3) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.add(t1, t2), 10000n), Nat.add(Nat.mul(t1, 10000n), Nat.mul(t2, 10000n)), LCw.cw.mul_add_r(t1, t2, 10000n)) : {Nat.add(_, Nat.mul(t3, 10000n)) == Nat.add(Nat.add(s1, s2), s3) : Nat}
  %Equal.sym(Nat, Nat.mul(t1, 10000n), s1, clw.red(r)) : {Nat.add(Nat.add(_, Nat.mul(t2, 10000n)), Nat.mul(t3, 10000n)) == Nat.add(Nat.add(s1, s2), s3) : Nat}
  %Equal.sym(Nat, Nat.mul(t2, 10000n), s2, clw.green(g)) : {Nat.add(Nat.add(s1, _), Nat.mul(t3, 10000n)) == Nat.add(Nat.add(s1, s2), s3) : Nat}
  %Equal.sym(Nat, Nat.mul(t3, 10000n), s3, clw.blue(b)) : {Nat.add(Nat.add(s1, s2), _) == Nat.add(Nat.add(s1, s2), s3) : Nat}
  {==}
