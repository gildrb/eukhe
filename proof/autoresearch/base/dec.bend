# eukhe: lemmas of the autoresearch decimal order (bend/autoresearch/dec.bend)

import Base
import ../../../bend/autoresearch/dec.bend as ArD
import ../../../laws/autoresearch/model.bend as Autoresearch
import ../../../spec/autoresearch/decimal.bend as SD

# Turning orders around
# ---------------------

def ad.nat_cmp_flip(x: Nat, y: Nat) -> {Nat.cmp(y, x) == Autoresearch.ar_flip(Nat.cmp(x, y)) : Cmp}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ad.nat_cmp_flip(p, q)

def ad.nat_cmp_refl(x: Nat) -> {Nat.cmp(x, x) == EQ{} : Cmp}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      ad.nat_cmp_refl(p)

def ad.then_flip(c: Cmp, -d: Cmp) -> {ArD.then(Autoresearch.ar_flip(c), Autoresearch.ar_flip(d)) == Autoresearch.ar_flip(ArD.then(c, d)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def ad.lex_flip(xs: List<&2, Nat>, ys: List<&2, Nat>) -> {ArD.lex(ys, xs) == Autoresearch.ar_flip(ArD.lex(xs, ys)) : Cmp}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      {==}
    case x <> xr Nil{}:
      {==}
    case +x <> +xr +y <> +yr:
      %Equal.sym(Cmp, ArD.lex(yr, xr), Autoresearch.ar_flip(ArD.lex(xr, yr)), ad.lex_flip(xr, yr)) : {ArD.then(Nat.cmp(y, x), _) == Autoresearch.ar_flip(ArD.then(Nat.cmp(x, y), ArD.lex(xr, yr))) : Cmp}
      %Equal.sym(Cmp, Nat.cmp(y, x), Autoresearch.ar_flip(Nat.cmp(x, y)), ad.nat_cmp_flip(x, y)) : {ArD.then(_, Autoresearch.ar_flip(ArD.lex(xr, yr))) == Autoresearch.ar_flip(ArD.then(Nat.cmp(x, y), ArD.lex(xr, yr))) : Cmp}
      ad.then_flip(Nat.cmp(x, y), ArD.lex(xr, yr))

def ad.lex_refl(xs: List<&2, Nat>) -> {ArD.lex(xs, xs) == EQ{} : Cmp}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +xr:
      %Equal.sym(Cmp, ArD.lex(xr, xr), EQ{}, ad.lex_refl(xr)) : {ArD.then(Nat.cmp(x, x), _) == EQ{} : Cmp}
      %Equal.sym(Cmp, Nat.cmp(x, x), EQ{}, ad.nat_cmp_refl(x)) : {ArD.then(_, EQ{}) == EQ{} : Cmp}
      {==}

# the padded magnitude order of y and x is that of x and y turned around
def ad.pad_flip(+x: List<&2, Nat>, +y: List<&2, Nat>) -> {ArD.mag.pad(y, x) == Autoresearch.ar_flip(ArD.mag.pad(x, y)) : Cmp}:
  ad.lex_flip(ArD.cat(ArD.zeros(Nat.sub(ArD.len(y), ArD.len(x))), x), ArD.cat(ArD.zeros(Nat.sub(ArD.len(x), ArD.len(y))), y))

def ad.pad_refl(+x: List<&2, Nat>) -> {ArD.mag.pad(x, x) == EQ{} : Cmp}:
  ad.lex_refl(ArD.cat(ArD.zeros(Nat.sub(ArD.len(x), ArD.len(x))), x))

# a sign cross case, read from the other side
def ad.cross_flip(p: Bool, q: Bool) -> {ArD.cross(Bool.or(q, p), GT{}) == Autoresearch.ar_flip(ArD.cross(Bool.or(p, q), LT{})) : Cmp}:
  match p q:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def ad.cross_flip_gt(p: Bool, q: Bool) -> {ArD.cross(Bool.or(q, p), LT{}) == Autoresearch.ar_flip(ArD.cross(Bool.or(p, q), GT{})) : Cmp}:
  match p q:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# Logic
# -----

def ad.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def ad.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ad.BD(_, A, Unit)
  Unit{}

def ad.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ad.absurd({False{} == True{} : Bool}, e)

def ad.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      ad.absurd({b == True{} : Bool}, e)

def ad.and_intro(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      ad.absurd({Bool.and(False{}, b) == True{} : Bool}, ha)

def ad.and_true(b: Bool) -> {b == Bool.and(b, True{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# Orders of pairs
# ---------------

def ad.then_eq(c: Cmp) -> {c == ArD.then(c, EQ{}) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

def ad.then_assoc(c: Cmp, -d: Cmp, -e: Cmp) -> {ArD.then(ArD.then(c, d), e) == ArD.then(c, ArD.then(d, e)) : Cmp}:
  match c:
    case LT{}:
      {==}
    case EQ{}:
      {==}
    case GT{}:
      {==}

# Numbers
# -------

def ad.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %ad.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def ad.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 1n+b), 1n+Nat.add(p, b), ad.add_succ(p, b))

# sub(n, m) + m is max(m, n), from either side
def ad.pad_len(m: Nat, n: Nat) -> {Nat.add(Nat.sub(n, m), m) == Nat.add(Nat.sub(m, n), n) : Nat}:
  match m n:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ad.add_zero(1n+q)
    case 1n+p 0n:
      Equal.sym(Nat, Nat.add(1n+p, 0n), 1n+p, ad.add_zero(1n+p))
    case 1n++p 1n++q:
      Equal.trans(Nat, Nat.add(Nat.sub(q, p), 1n+p), 1n+Nat.add(Nat.sub(q, p), p), Nat.add(Nat.sub(p, q), 1n+q),
        ad.add_succ(Nat.sub(q, p), p),
        Equal.trans(Nat, 1n+Nat.add(Nat.sub(q, p), p), 1n+Nat.add(Nat.sub(p, q), q), Nat.add(Nat.sub(p, q), 1n+q),
          Equal.cong(Nat, Nat, k => 1n+k, Nat.add(Nat.sub(q, p), p), Nat.add(Nat.sub(p, q), q), ad.pad_len(p, q)),
          Equal.sym(Nat, Nat.add(Nat.sub(p, q), 1n+q), 1n+Nat.add(Nat.sub(p, q), q), ad.add_succ(Nat.sub(p, q), q))))

def ad.is_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ad.is_eq_refl(p)

def ad.is_eq_of(+m: Nat, -n: Nat, e: {m == n : Nat}) -> {Nat.is_eq(m, n) == True{} : Bool}:
  %e : {Nat.is_eq(m, _) == True{} : Bool}
  ad.is_eq_refl(m)

# x below n is below n + z
def ad.lt_add(x: Nat, n: Nat, -z: Nat, h: {Nat.is_lt(x, n) == True{} : Bool}) -> {Nat.cmp(x, Nat.add(n, z)) == LT{} : Cmp}:
  match x n:
    case 0n 0n:
      ad.absurd({Nat.cmp(0n, Nat.add(0n, z)) == LT{} : Cmp}, h)
    case 0n 1n+m:
      {==}
    case 1n+p 0n:
      ad.absurd({Nat.cmp(1n+p, Nat.add(0n, z)) == LT{} : Cmp}, h)
    case 1n+p 1n+m:
      ad.lt_add(p, m, z, h)

def ad.gt_add(y: Nat, n: Nat, -z: Nat, h: {Nat.is_lt(y, n) == True{} : Bool}) -> {Nat.cmp(Nat.add(n, z), y) == GT{} : Cmp}:
  match y n:
    case 0n 0n:
      ad.absurd({Nat.cmp(Nat.add(0n, z), 0n) == GT{} : Cmp}, h)
    case 0n 1n+m:
      {==}
    case 1n+p 0n:
      ad.absurd({Nat.cmp(Nat.add(0n, z), 1n+p) == GT{} : Cmp}, h)
    case 1n+p 1n+m:
      ad.gt_add(p, m, z, h)

# appending a digit keeps the order of the numbers before it, ties broken
# by the digits
def ad.digit_cmp(a: Nat, b: Nat, +x: Nat, +y: Nat, hx: {Nat.is_lt(x, 10n) == True{} : Bool}, hy: {Nat.is_lt(y, 10n) == True{} : Bool}) -> {Nat.cmp(Nat.add(Nat.mul(a, 10n), x), Nat.add(Nat.mul(b, 10n), y)) == ArD.then(Nat.cmp(a, b), Nat.cmp(x, y)) : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ad.lt_add(x, 10n, Nat.add(Nat.mul(q, 10n), y), hx)
    case 1n+p 0n:
      ad.gt_add(y, 10n, Nat.add(Nat.mul(p, 10n), x), hy)
    case 1n+p 1n+q:
      ad.digit_cmp(p, q, x, y, hx, hy)

# Digit lists
# -----------

def ad.digits_cat(xs: List<&2, Nat>, -ys: List<&2, Nat>, +hx: {SD.digits_ok(xs) == True{} : Bool}, hy: {SD.digits_ok(ys) == True{} : Bool}) -> {SD.digits_ok(ArD.cat(xs, ys)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hy
    case +x <> +xr:
      ad.and_intro(Nat.is_lt(x, 10n), SD.digits_ok(ArD.cat(xr, ys)), ad.and_l(Nat.is_lt(x, 10n), SD.digits_ok(xr), hx), ad.digits_cat(xr, ys, ad.and_r(Nat.is_lt(x, 10n), SD.digits_ok(xr), hx), hy))

def ad.digits_zeros(k: Nat) -> {SD.digits_ok(ArD.zeros(k)) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      ad.digits_zeros(j)

def ad.len_cat(xs: List<&2, Nat>, -ys: List<&2, Nat>) -> {ArD.len(ArD.cat(xs, ys)) == Nat.add(ArD.len(xs), ArD.len(ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> xr:
      Equal.cong(Nat, Nat, k => 1n+k, ArD.len(ArD.cat(xr, ys)), Nat.add(ArD.len(xr), ArD.len(ys)), ad.len_cat(xr, ys))

def ad.len_zeros(k: Nat) -> {ArD.len(ArD.zeros(k)) == k : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      Equal.cong(Nat, Nat, n => 1n+n, ArD.len(ArD.zeros(j)), j, ad.len_zeros(j))

# k zeros, then xs: of length k + |xs|
def ad.len_pad(+k: Nat, +xs: List<&2, Nat>) -> {ArD.len(ArD.cat(ArD.zeros(k), xs)) == Nat.add(k, ArD.len(xs)) : Nat}:
  Equal.trans(Nat, ArD.len(ArD.cat(ArD.zeros(k), xs)), Nat.add(ArD.len(ArD.zeros(k)), ArD.len(xs)), Nat.add(k, ArD.len(xs)),
    ad.len_cat(ArD.zeros(k), xs),
    Equal.cong(Nat, Nat, n => Nat.add(n, ArD.len(xs)), ArD.len(ArD.zeros(k)), k, ad.len_zeros(k)))

# The value of digits
# -------------------

def ad.num_cat(xs: List<&2, Nat>, -ys: List<&2, Nat>, acc: Nat) -> {SD.num.go(ArD.cat(xs, ys), acc) == SD.num.go(ys, SD.num.go(xs, acc)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case x <> xr:
      ad.num_cat(xr, ys, Nat.add(Nat.mul(acc, 10n), x))

def ad.num_zeros0(k: Nat) -> {SD.num.go(ArD.zeros(k), 0n) == 0n : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      ad.num_zeros0(j)

def ad.num_zeros(k: Nat, +c: Nat) -> {SD.num.go(ArD.zeros(k), c) == SD.shift(k, c) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      %Equal.sym(Nat, Nat.add(Nat.mul(c, 10n), 0n), Nat.mul(c, 10n), ad.add_zero(Nat.mul(c, 10n))) : {SD.num.go(ArD.zeros(j), _) == SD.shift(j, Nat.mul(c, 10n)) : Nat}
      ad.num_zeros(j, Nat.mul(c, 10n))

# leading zeros are worth nothing
def ad.num_pad(+k: Nat, +xs: List<&2, Nat>) -> {SD.num.go(ArD.cat(ArD.zeros(k), xs), 0n) == SD.num.go(xs, 0n) : Nat}:
  Equal.trans(Nat, SD.num.go(ArD.cat(ArD.zeros(k), xs), 0n), SD.num.go(xs, SD.num.go(ArD.zeros(k), 0n)), SD.num.go(xs, 0n),
    ad.num_cat(ArD.zeros(k), xs, 0n),
    Equal.cong(Nat, Nat, c => SD.num.go(xs, c), SD.num.go(ArD.zeros(k), 0n), 0n, ad.num_zeros0(k)))

# trailing zeros shift
def ad.num_shift(+xs: List<&2, Nat>, +k: Nat) -> {SD.num.go(ArD.cat(xs, ArD.zeros(k)), 0n) == SD.shift(k, SD.num.go(xs, 0n)) : Nat}:
  Equal.trans(Nat, SD.num.go(ArD.cat(xs, ArD.zeros(k)), 0n), SD.num.go(ArD.zeros(k), SD.num.go(xs, 0n)), SD.shift(k, SD.num.go(xs, 0n)),
    ad.num_cat(xs, ArD.zeros(k), 0n),
    ad.num_zeros(k, SD.num.go(xs, 0n)))

# two digit lists of one length compare as their numbers, after a and b
def ad.num_lex(xs: List<&2, Nat>, ys: List<&2, Nat>, +a: Nat, +b: Nat, hl: {Nat.is_eq(ArD.len(xs), ArD.len(ys)) == True{} : Bool}, +hx: {SD.digits_ok(xs) == True{} : Bool}, +hy: {SD.digits_ok(ys) == True{} : Bool}) -> {Nat.cmp(SD.num.go(xs, a), SD.num.go(ys, b)) == ArD.then(Nat.cmp(a, b), ArD.lex(xs, ys)) : Cmp}:
  match xs ys:
    case Nil{} Nil{}:
      ad.then_eq(Nat.cmp(a, b))
    case Nil{} y <> yr:
      ad.absurd({Nat.cmp(a, SD.num.go(yr, Nat.add(Nat.mul(b, 10n), y))) == ArD.then(Nat.cmp(a, b), LT{}) : Cmp}, hl)
    case x <> xr Nil{}:
      ad.absurd({Nat.cmp(SD.num.go(xr, Nat.add(Nat.mul(a, 10n), x)), b) == ArD.then(Nat.cmp(a, b), GT{}) : Cmp}, hl)
    case +x <> +xr +y <> +yr:
      %ad.then_assoc(Nat.cmp(a, b), Nat.cmp(x, y), ArD.lex(xr, yr)) : {Nat.cmp(SD.num.go(xr, Nat.add(Nat.mul(a, 10n), x)), SD.num.go(yr, Nat.add(Nat.mul(b, 10n), y))) == _ : Cmp}
      %ad.digit_cmp(a, b, x, y, ad.and_l(Nat.is_lt(x, 10n), SD.digits_ok(xr), hx), ad.and_l(Nat.is_lt(y, 10n), SD.digits_ok(yr), hy)) : {Nat.cmp(SD.num.go(xr, Nat.add(Nat.mul(a, 10n), x)), SD.num.go(yr, Nat.add(Nat.mul(b, 10n), y))) == ArD.then(_, ArD.lex(xr, yr)) : Cmp}
      ad.num_lex(xr, yr, Nat.add(Nat.mul(a, 10n), x), Nat.add(Nat.mul(b, 10n), y), hl, ad.and_r(Nat.is_lt(x, 10n), SD.digits_ok(xr), hx), ad.and_r(Nat.is_lt(y, 10n), SD.digits_ok(yr), hy))

# the padded order of two digit lists is the order of their numbers
def ad.pad_exact(+x: List<&2, Nat>, +y: List<&2, Nat>, +hx: {SD.digits_ok(x) == True{} : Bool}, +hy: {SD.digits_ok(y) == True{} : Bool}) -> {ArD.mag.pad(x, y) == Nat.cmp(SD.num.go(x, 0n), SD.num.go(y, 0n)) : Cmp}:
  +kx = Nat.sub(ArD.len(y), ArD.len(x))
  +ky = Nat.sub(ArD.len(x), ArD.len(y))
  +px = ArD.cat(ArD.zeros(kx), x)
  +py = ArD.cat(ArD.zeros(ky), y)
  +hl = ad.is_eq_of(ArD.len(px), ArD.len(py),
    Equal.trans(Nat, ArD.len(px), Nat.add(kx, ArD.len(x)), ArD.len(py),
      ad.len_pad(kx, x),
      Equal.trans(Nat, Nat.add(kx, ArD.len(x)), Nat.add(ky, ArD.len(y)), ArD.len(py),
        ad.pad_len(ArD.len(x), ArD.len(y)),
        Equal.sym(Nat, ArD.len(py), Nat.add(ky, ArD.len(y)), ad.len_pad(ky, y)))))
  %ad.num_pad(kx, x) : {ArD.lex(px, py) == Nat.cmp(_, SD.num.go(y, 0n)) : Cmp}
  %ad.num_pad(ky, y) : {ArD.lex(px, py) == Nat.cmp(SD.num.go(px, 0n), _) : Cmp}
  Equal.sym(Cmp, Nat.cmp(SD.num.go(px, 0n), SD.num.go(py, 0n)), ArD.lex(px, py), ad.num_lex(px, py, 0n, 0n, hl, ad.digits_cat(ArD.zeros(kx), x, ad.digits_zeros(kx), hx), ad.digits_cat(ArD.zeros(ky), y, ad.digits_zeros(ky), hy)))

# the shipped magnitude order is the order of the values a·10^sb, b·10^sa
def ad.mag_exact(+da: List<&2, Nat>, +sa: Nat, +db: List<&2, Nat>, +sb: Nat, wa: {SD.digits_ok(da) == True{} : Bool}, wb: {SD.digits_ok(db) == True{} : Bool}) -> {ArD.mag(da, sa, db, sb) == Nat.cmp(SD.shift(sb, SD.num(da)), SD.shift(sa, SD.num(db))) : Cmp}:
  +x = ArD.cat(da, ArD.zeros(sb))
  +y = ArD.cat(db, ArD.zeros(sa))
  %ad.num_shift(da, sb) : {ArD.mag.pad(x, y) == Nat.cmp(_, SD.shift(sa, SD.num.go(db, 0n))) : Cmp}
  %ad.num_shift(db, sa) : {ArD.mag.pad(x, y) == Nat.cmp(SD.num.go(x, 0n), _) : Cmp}
  ad.pad_exact(x, y, ad.digits_cat(da, ArD.zeros(sb), wa, ad.digits_zeros(sb)), ad.digits_cat(db, ArD.zeros(sa), wb, ad.digits_zeros(sa)))

# Zero
# ----

def ad.zero_digit(d: Nat, -q: Bool) -> {Bool.and(Nat.is_eq(d, 0n), Bool.not(q)) == Bool.and(True{}, Bool.not(Bool.or(Nat.is_ne(d, 0n), q))) : Bool}:
  match d:
    case 0n:
      {==}
    case 1n+e:
      {==}

def ad.zero_step(acc: Nat, d: Nat, -q: Bool) -> {Bool.and(Nat.is_eq(Nat.add(Nat.mul(acc, 10n), d), 0n), Bool.not(q)) == Bool.and(Nat.is_eq(acc, 0n), Bool.not(Bool.or(Nat.is_ne(d, 0n), q))) : Bool}:
  match acc:
    case 0n:
      ad.zero_digit(d, q)
    case 1n+p:
      {==}

# the number after acc is 0 just when acc is and every digit is
def ad.zero_go(ds: List<&2, Nat>, +acc: Nat) -> {Nat.is_eq(SD.num.go(ds, acc), 0n) == Bool.and(Nat.is_eq(acc, 0n), Bool.not(ArD.nz(ds))) : Bool}:
  match ds:
    case Nil{}:
      ad.and_true(Nat.is_eq(acc, 0n))
    case +d <> +t:
      Equal.trans(Bool, Nat.is_eq(SD.num.go(t, Nat.add(Nat.mul(acc, 10n), d)), 0n), Bool.and(Nat.is_eq(Nat.add(Nat.mul(acc, 10n), d), 0n), Bool.not(ArD.nz(t))), Bool.and(Nat.is_eq(acc, 0n), Bool.not(Bool.or(Nat.is_ne(d, 0n), ArD.nz(t)))),
        ad.zero_go(t, Nat.add(Nat.mul(acc, 10n), d)),
        ad.zero_step(acc, d, ArD.nz(t)))

def ad.nz_zero(ds: List<&2, Nat>) -> {Bool.not(ArD.nz(ds)) == SD.zero(ds) : Bool}:
  Equal.sym(Bool, SD.zero(ds), Bool.not(ArD.nz(ds)), ad.zero_go(ds, 0n))

def ad.cross_bools(p: Bool, q: Bool, -c: Cmp) -> {ArD.cross(Bool.or(p, q), c) == SD.order.cross(Bool.and(Bool.not(p), Bool.not(q)), c) : Cmp}:
  match p q:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# a negative against a positive: the shipped cross order is the spec's
def ad.cross_exact(+da: List<&2, Nat>, +db: List<&2, Nat>, +c: Cmp) -> {ArD.cross(Bool.or(ArD.nz(da), ArD.nz(db)), c) == SD.order.cross(Bool.and(SD.zero(da), SD.zero(db)), c) : Cmp}:
  %ad.nz_zero(da) : {ArD.cross(Bool.or(ArD.nz(da), ArD.nz(db)), c) == SD.order.cross(Bool.and(_, SD.zero(db)), c) : Cmp}
  %ad.nz_zero(db) : {ArD.cross(Bool.or(ArD.nz(da), ArD.nz(db)), c) == SD.order.cross(Bool.and(Bool.not(ArD.nz(da)), _), c) : Cmp}
  ad.cross_bools(ArD.nz(da), ArD.nz(db), c)
