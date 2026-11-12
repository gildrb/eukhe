# eukhe: lemmas of the proofs of area budget about children (bend/budget.bend
# carve, close): sums and differences of Nat, when no dimension lacks, what
# a carve and a close answer in one dimension

import Base
import ../../../bend/budget.bend as B
import ../../../spec/budget/ledger.bend as S
import ./settle.bend as BS
import ./reserve.bend as BR

# Logic
# -----

def bt.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# a premise False == True proves anything
def bt.absurd_ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : bt.IfF(_, G)
  Unit{}

def bt.IfNone(m: Maybe<&2, B.Dim>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{d}:
      Unit

# a dimension that lacks is no fit
def bt.absurd_some(-G: Type, -d: B.Dim, e: {Some{d} == None{} : Maybe<&2, B.Dim>}) -> G:
  %e : bt.IfNone(_, G)
  Unit{}

# Nat: sums
# ---------

def bt.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %bt.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def bt.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %bt.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def bt.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %bt.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def bt.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, bt.add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), bt.add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %bt.add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# a + (b + c) = b + (a + c)
def bt.add_lcomm(+a: Nat, +b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  %bt.add_assoc(a, b, c) : {_ == Nat.add(b, Nat.add(a, c)) : Nat}
  %Equal.sym(Nat, Nat.add(a, b), Nat.add(b, a), bt.add_comm(a, b)) : {Nat.add(_, c) == Nat.add(b, Nat.add(a, c)) : Nat}
  bt.add_assoc(b, a, c)

# (a + b) + c = (a + c) + b
def bt.add_rcomm(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  match a:
    case 0n:
      bt.add_comm(b, c)
    case 1n+p:
      %bt.add_rcomm(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

# b + (a + c) = (a + b) + c
def bt.add_rot(+a: Nat, +b: Nat, -c: Nat) -> {Nat.add(b, Nat.add(a, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  %bt.add_lcomm(a, b, c) : {_ == Nat.add(Nat.add(a, b), c) : Nat}
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), bt.add_assoc(a, b, c))

def bt.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# k + a = k + b: a = b
def bt.add_cancel(k: Nat, -a: Nat, -b: Nat, e: {Nat.add(k, a) == Nat.add(k, b) : Nat}) -> {a == b : Nat}:
  match k:
    case 0n:
      e
    case 1n+p:
      bt.add_cancel(p, a, b, Equal.cong(Nat, Nat, x => bt.pred(x), 1n+Nat.add(p, a), 1n+Nat.add(p, b), e))

# Nat: differences and order
# --------------------------

def bt.sub_zero(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# n + (x - n) = x when n <= x
def bt.sub_add(+n: Nat, +x: Nat, +e: {Nat.is_le(n, x) == True{} : Bool}) -> {Nat.add(n, Nat.sub(x, n)) == x : Nat}:
  match n x:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      bt.absurd_ft({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, e)
    case 1n+p 1n+q:
      %bt.sub_add(p, q, e) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

# (x - n) + n = x when n <= x
def bt.add_sub(+n: Nat, +x: Nat, +e: {Nat.is_le(n, x) == True{} : Bool}) -> {Nat.add(Nat.sub(x, n), n) == x : Nat}:
  %bt.add_comm(n, Nat.sub(x, n)) : {_ == x : Nat}
  bt.sub_add(n, x, e)

# (w + l) - w = l
def bt.sub_add_l(w: Nat, +l: Nat) -> {Nat.sub(Nat.add(w, l), w) == l : Nat}:
  match w:
    case 0n:
      bt.sub_zero(l)
    case 1n+q:
      bt.sub_add_l(q, l)

# (l + w) - w = l
def bt.sub_add_r(+l: Nat, +w: Nat) -> {Nat.sub(Nat.add(l, w), w) == l : Nat}:
  %bt.add_comm(w, l) : {Nat.sub(_, w) == l : Nat}
  bt.sub_add_l(w, l)

# (a - c) + c = a + (c - a): the larger of the two
def bt.max(a: Nat, c: Nat) -> {Nat.add(Nat.sub(a, c), c) == Nat.add(a, Nat.sub(c, a)) : Nat}:
  match a c:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n++p 1n++q:
      %bt.max(p, q) : {Nat.add(Nat.sub(p, q), 1n+q) == 1n+_ : Nat}
      bt.add_succ(Nat.sub(p, q), q)

# n <= x when n + z <= x
def bt.le_add_l(+n: Nat, -z: Nat, +x: Nat, +e: {Nat.is_le(Nat.add(n, z), x) == True{} : Bool}) -> {Nat.is_le(n, x) == True{} : Bool}:
  match n x:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      bt.absurd_ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      bt.le_add_l(p, z, q, e)

# z <= x - n when n + z <= x
def bt.le_sub(+n: Nat, -z: Nat, +x: Nat, +e: {Nat.is_le(Nat.add(n, z), x) == True{} : Bool}) -> {Nat.is_le(z, Nat.sub(x, n)) == True{} : Bool}:
  match n x:
    case 0n 0n:
      e
    case 0n 1n+q:
      e
    case 1n+p 0n:
      bt.absurd_ft({Nat.is_le(z, Nat.sub(0n, 1n+p)) == True{} : Bool}, e)
    case 1n+p 1n+q:
      bt.le_sub(p, z, q, e)

# Nat: a close in one dimension
# -----------------------------

# ((a + b) + y) + c = a + ((b + c) + y)
def bt.ac1(a: Nat, +b: Nat, +y: Nat, +c: Nat) -> {Nat.add(Nat.add(Nat.add(a, b), y), c) == Nat.add(a, Nat.add(Nat.add(b, c), y)) : Nat}:
  match a:
    case 0n:
      bt.add_rcomm(b, y, c)
    case 1n+p:
      %bt.ac1(p, b, y, c) : {1n+Nat.add(Nat.add(Nat.add(p, b), y), c) == 1n+_ : Nat}
      {==}

# (a + (g + w)) + y = (a + (g + y)) + w
def bt.swap_in(a: Nat, +g: Nat, +w: Nat, +y: Nat) -> {Nat.add(Nat.add(a, Nat.add(g, w)), y) == Nat.add(Nat.add(a, Nat.add(g, y)), w) : Nat}:
  match a:
    case 0n:
      bt.add_rcomm(g, w, y)
    case 1n+p:
      %bt.swap_in(p, g, w, y) : {1n+Nat.add(Nat.add(p, Nat.add(g, w)), y) == 1n+_ : Nat}
      {==}

# with co added on both sides: x + co is the larger of pf + cf and co, and
# co + g is cf + cs
def bt.core_co(+co: Nat, +x: Nat, +y: Nat, +g: Nat, +pf: Nat, +cf: Nat, +cs: Nat, m: {Nat.add(Nat.add(pf, cf), y) == Nat.add(x, co) : Nat}, t: {Nat.add(cf, cs) == Nat.add(co, g) : Nat}) -> {Nat.add(co, Nat.add(x, cs)) == Nat.add(co, Nat.add(pf, Nat.add(g, y))) : Nat}:
  %bt.add_assoc(co, x, cs) : {_ == Nat.add(co, Nat.add(pf, Nat.add(g, y))) : Nat}
  %bt.add_comm(x, co) : {Nat.add(_, cs) == Nat.add(co, Nat.add(pf, Nat.add(g, y))) : Nat}
  %m : {Nat.add(_, cs) == Nat.add(co, Nat.add(pf, Nat.add(g, y))) : Nat}
  %bt.add_lcomm(pf, co, Nat.add(g, y)) : {Nat.add(Nat.add(Nat.add(pf, cf), y), cs) == _ : Nat}
  %bt.add_assoc(co, g, y) : {Nat.add(Nat.add(Nat.add(pf, cf), y), cs) == Nat.add(pf, _) : Nat}
  %t : {Nat.add(Nat.add(Nat.add(pf, cf), y), cs) == Nat.add(pf, Nat.add(_, y)) : Nat}
  bt.ac1(pf, cf, y, cs)

# what is left of the parent's free and the child's, with the child's spend,
# is the parent's free, what returns to lent and the new overrun, when the
# child's overrun co is within what it was funded (cf + cs)
def bt.core(+pf: Nat, +cf: Nat, +cs: Nat, +co: Nat, +e: {Nat.is_le(co, Nat.add(cf, cs)) == True{} : Bool}) -> {Nat.add(Nat.sub(Nat.add(pf, cf), co), cs) == Nat.add(pf, Nat.add(Nat.sub(Nat.add(cf, cs), co), Nat.sub(co, Nat.add(pf, cf)))) : Nat}:
  bt.add_cancel(co, Nat.add(Nat.sub(Nat.add(pf, cf), co), cs), Nat.add(pf, Nat.add(Nat.sub(Nat.add(cf, cs), co), Nat.sub(co, Nat.add(pf, cf)))), bt.core_co(co, Nat.sub(Nat.add(pf, cf), co), Nat.sub(co, Nat.add(pf, cf)), Nat.sub(Nat.add(cf, cs), co), pf, cf, cs, Equal.sym(Nat, Nat.add(Nat.sub(Nat.add(pf, cf), co), co), Nat.add(Nat.add(pf, cf), Nat.sub(co, Nat.add(pf, cf))), bt.max(Nat.add(pf, cf), co)), Equal.sym(Nat, Nat.add(co, Nat.sub(Nat.add(cf, cs), co)), Nat.add(cf, cs), bt.sub_add(co, Nat.add(cf, cs), e))))

# (x + cs) + (hh + (ps + r)) = x + (hh + ((ps + cs) + r))
def bt.lhs_shape(+x: Nat, +hh: Nat, +ps: Nat, +cs: Nat, +r: Nat) -> {Nat.add(Nat.add(x, cs), Nat.add(hh, Nat.add(ps, r))) == Nat.add(x, Nat.add(hh, Nat.add(Nat.add(ps, cs), r))) : Nat}:
  %bt.add_rot(ps, cs, r) : {Nat.add(Nat.add(x, cs), Nat.add(hh, Nat.add(ps, r))) == Nat.add(x, Nat.add(hh, _)) : Nat}
  %bt.add_lcomm(cs, hh, Nat.add(ps, r)) : {Nat.add(Nat.add(x, cs), Nat.add(hh, Nat.add(ps, r))) == Nat.add(x, _) : Nat}
  bt.add_assoc(x, cs, Nat.add(hh, Nat.add(ps, r)))

# ((pf + (g + y)) + (hh + (ps + r))) + po = (pf + (hh + (ps + (g + r)))) + (po + y)
def bt.rhs_shape(+pf: Nat, +hh: Nat, +ps: Nat, +g: Nat, +r: Nat, +po: Nat, +y: Nat) -> {Nat.add(Nat.add(Nat.add(pf, Nat.add(g, y)), Nat.add(hh, Nat.add(ps, r))), po) == Nat.add(Nat.add(pf, Nat.add(hh, Nat.add(ps, Nat.add(g, r)))), Nat.add(po, y)) : Nat}:
  %bt.add_lcomm(g, ps, r) : {Nat.add(Nat.add(Nat.add(pf, Nat.add(g, y)), Nat.add(hh, Nat.add(ps, r))), po) == Nat.add(Nat.add(pf, Nat.add(hh, _)), Nat.add(po, y)) : Nat}
  %bt.add_lcomm(g, hh, Nat.add(ps, r)) : {Nat.add(Nat.add(Nat.add(pf, Nat.add(g, y)), Nat.add(hh, Nat.add(ps, r))), po) == Nat.add(Nat.add(pf, _), Nat.add(po, y)) : Nat}
  %bt.add_comm(y, po) : {Nat.add(Nat.add(Nat.add(pf, Nat.add(g, y)), Nat.add(hh, Nat.add(ps, r))), po) == Nat.add(Nat.add(pf, Nat.add(g, Nat.add(hh, Nat.add(ps, r)))), _) : Nat}
  %bt.add_assoc(Nat.add(pf, Nat.add(g, Nat.add(hh, Nat.add(ps, r)))), y, po) : {Nat.add(Nat.add(Nat.add(pf, Nat.add(g, y)), Nat.add(hh, Nat.add(ps, r))), po) == _ : Nat}
  %bt.swap_in(pf, g, Nat.add(hh, Nat.add(ps, r)), y) : {Nat.add(_, po) == Nat.add(Nat.add(Nat.add(pf, Nat.add(g, Nat.add(hh, Nat.add(ps, r)))), y), po) : Nat}
  {==}

# the parts of both sides that the close does not touch (held hh, spent ps,
# overrun po) frame the core; r is what stays lent, g + r what was lent
def bt.frame(+x: Nat, +cs: Nat, +pf: Nat, +g: Nat, +y: Nat, +r: Nat, +hh: Nat, +ps: Nat, +po: Nat, -pl: Nat, c1: {Nat.add(x, cs) == Nat.add(pf, Nat.add(g, y)) : Nat}, c2: {Nat.add(g, r) == pl : Nat}) -> {Nat.add(Nat.add(x, Nat.add(hh, Nat.add(Nat.add(ps, cs), r))), po) == Nat.add(Nat.add(pf, Nat.add(hh, Nat.add(ps, pl))), Nat.add(po, y)) : Nat}:
  %c2 : {Nat.add(Nat.add(x, Nat.add(hh, Nat.add(Nat.add(ps, cs), r))), po) == Nat.add(Nat.add(pf, Nat.add(hh, Nat.add(ps, _))), Nat.add(po, y)) : Nat}
  %bt.rhs_shape(pf, hh, ps, g, r, po, y) : {Nat.add(Nat.add(x, Nat.add(hh, Nat.add(Nat.add(ps, cs), r))), po) == _ : Nat}
  %bt.lhs_shape(x, hh, ps, cs, r) : {Nat.add(_, po) == Nat.add(Nat.add(Nat.add(pf, Nat.add(g, y)), Nat.add(hh, Nat.add(ps, r))), po) : Nat}
  %c1 : {Nat.add(Nat.add(Nat.add(x, cs), Nat.add(hh, Nat.add(ps, r))), po) == Nat.add(Nat.add(_, Nat.add(hh, Nat.add(ps, r))), po) : Nat}
  {==}

# a close conserves the parent's budget in one dimension: free pf, held hh,
# spent ps, lent pl, overrun po; the child's free cf, spent cs, overrun co
def bt.conserve(+pf: Nat, +cf: Nat, +cs: Nat, +co: Nat, +ps: Nat, +pl: Nat, +po: Nat, +hh: Nat, +e1: {Nat.is_le(co, Nat.add(cf, cs)) == True{} : Bool}, +e2: {Nat.is_le(Nat.sub(Nat.add(cf, cs), co), pl) == True{} : Bool}) -> {Nat.add(Nat.add(Nat.sub(Nat.add(pf, cf), co), Nat.add(hh, Nat.add(Nat.add(ps, cs), Nat.sub(pl, Nat.sub(Nat.add(cf, cs), co))))), po) == Nat.add(Nat.add(pf, Nat.add(hh, Nat.add(ps, pl))), Nat.add(po, Nat.sub(co, Nat.add(pf, cf)))) : Nat}:
  bt.frame(Nat.sub(Nat.add(pf, cf), co), cs, pf, Nat.sub(Nat.add(cf, cs), co), Nat.sub(co, Nat.add(pf, cf)), Nat.sub(pl, Nat.sub(Nat.add(cf, cs), co)), hh, ps, po, pl, bt.core(pf, cf, cs, co, e1), bt.sub_add(Nat.sub(Nat.add(cf, cs), co), pl, e2))

# Amounts
# -------

def bt.amt_eq(-a1: Nat, -a2: Nat, -b1: Nat, -b2: Nat, -c1: Nat, -c2: Nat, -d1: Nat, -d2: Nat, ea: {a1 == a2 : Nat}, eb: {b1 == b2 : Nat}, ec: {c1 == c2 : Nat}, ed: {d1 == d2 : Nat}) -> {B.Amt{a1, b1, c1, d1} == B.Amt{a2, b2, c2, d2} : B.Amt}:
  %ea : {B.Amt{a1, b1, c1, d1} == B.Amt{_, b2, c2, d2} : B.Amt}
  %eb : {B.Amt{a1, b1, c1, d1} == B.Amt{a1, _, c2, d2} : B.Amt}
  %ec : {B.Amt{a1, b1, c1, d1} == B.Amt{a1, b1, _, d2} : B.Amt}
  %ed : {B.Amt{a1, b1, c1, d1} == B.Amt{a1, b1, c1, _} : B.Amt}
  {==}

# x and nothing is x
def bt.add4_zero(x: B.Amt) -> {B.add4(x, B.zero()) == x : B.Amt}:
  match x:
    case B.Amt{+a, +b, +c, +d}:
      bt.amt_eq(Nat.add(a, 0n), a, Nat.add(b, 0n), b, Nat.add(c, 0n), c, Nat.add(d, 0n), d, bt.add_zero(a), bt.add_zero(b), bt.add_zero(c), bt.add_zero(d))

# ((f - w) + w) - 0 = f when w <= f
def bt.back(+f: Nat, +w: Nat, +e: {Nat.is_le(w, f) == True{} : Bool}) -> {Nat.sub(Nat.add(Nat.sub(f, w), w), 0n) == f : Nat}:
  %bt.add_sub(w, f, e) : {Nat.sub(Nat.add(Nat.sub(f, w), w), 0n) == _ : Nat}
  bt.sub_zero(Nat.add(Nat.sub(f, w), w))

# what was carved out of f and comes back whole is f, when w was within f
def bt.give_back(f: B.Amt, w: B.Amt, +ea: {Nat.is_le(S.at(B.Cost{}, w), S.at(B.Cost{}, f)) == True{} : Bool}, +eb: {Nat.is_le(S.at(B.Tok{}, w), S.at(B.Tok{}, f)) == True{} : Bool}, +ec: {Nat.is_le(S.at(B.Calls{}, w), S.at(B.Calls{}, f)) == True{} : Bool}, +ed: {Nat.is_le(S.at(B.Reqs{}, w), S.at(B.Reqs{}, f)) == True{} : Bool}) -> {B.sub4(B.add4(B.sub4(f, w), w), B.zero()) == f : B.Amt}:
  match f w:
    case B.Amt{+fa, +fb, +fc, +fd} B.Amt{+wa, +wb, +wc, +wd}:
      bt.amt_eq(Nat.sub(Nat.add(Nat.sub(fa, wa), wa), 0n), fa, Nat.sub(Nat.add(Nat.sub(fb, wb), wb), 0n), fb, Nat.sub(Nat.add(Nat.sub(fc, wc), wc), 0n), fc, Nat.sub(Nat.add(Nat.sub(fd, wd), wd), 0n), fd, bt.back(fa, wa, ea), bt.back(fb, wb, eb), bt.back(fc, wc, ec), bt.back(fd, wd, ed))

# w = (w + 0) - 0
def bt.wz(+w: Nat) -> {w == Nat.sub(Nat.add(w, 0n), 0n) : Nat}:
  Equal.sym(Nat, Nat.sub(Nat.add(w, 0n), 0n), w, Equal.trans(Nat, Nat.sub(Nat.add(w, 0n), 0n), Nat.add(w, 0n), w, bt.sub_zero(Nat.add(w, 0n)), bt.add_zero(w)))

# (l + w) - ((w + 0) - 0) = l
def bt.lback(+l: Nat, +w: Nat) -> {Nat.sub(Nat.add(l, w), Nat.sub(Nat.add(w, 0n), 0n)) == l : Nat}:
  %bt.wz(w) : {Nat.sub(Nat.add(l, w), _) == l : Nat}
  bt.sub_add_r(l, w)

# what was lent to a child that spent nothing and comes back is not lent
def bt.lent_back(l: B.Amt, w: B.Amt) -> {B.sub4(B.add4(l, w), B.sub4(B.add4(w, B.zero()), B.zero())) == l : B.Amt}:
  match l w:
    case B.Amt{+la, +lb, +lc, +ld} B.Amt{+wa, +wb, +wc, +wd}:
      bt.amt_eq(Nat.sub(Nat.add(la, wa), Nat.sub(Nat.add(wa, 0n), 0n)), la, Nat.sub(Nat.add(lb, wb), Nat.sub(Nat.add(wb, 0n), 0n)), lb, Nat.sub(Nat.add(lc, wc), Nat.sub(Nat.add(wc, 0n), 0n)), lc, Nat.sub(Nat.add(ld, wd), Nat.sub(Nat.add(wd, 0n), 0n)), ld, bt.lback(la, wa), bt.lback(lb, wb), bt.lback(lc, wc), bt.lback(ld, wd))

# no overrun of the child: the parent's overrun stays
def bt.over_back(o: B.Amt, x: B.Amt) -> {B.add4(o, B.sub4(B.zero(), x)) == o : B.Amt}:
  match o x:
    case B.Amt{+oa, +ob, +oc, +od} B.Amt{xa, xb, xc, xd}:
      bt.amt_eq(Nat.add(oa, 0n), oa, Nat.add(ob, 0n), ob, Nat.add(oc, 0n), oc, Nat.add(od, 0n), od, bt.add_zero(oa), bt.add_zero(ob), bt.add_zero(oc), bt.add_zero(od))

# x is zero by the code's test exactly when it is by the spec's
def bt.zero_none(x: B.Amt) -> {B.is_zero4(x) == S.none4(x) : Bool}:
  match x:
    case B.Amt{a, b, c, d}:
      {==}

# Fitting
# -------

# no dimension lacks: the first test holds
def bt.ok(b: Bool, -d: B.Dim, -rest: Maybe<&2, B.Dim>, e: {B.lack.at(b, d, rest) == None{} : Maybe<&2, B.Dim>}) -> {b == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      bt.absurd_some({False{} == True{} : Bool}, d, e)

# no dimension lacks: none of the rest lacks
def bt.rest(b: Bool, -d: B.Dim, -rest: Maybe<&2, B.Dim>, e: {B.lack.at(b, d, rest) == None{} : Maybe<&2, B.Dim>}) -> {rest == None{} : Maybe<&2, B.Dim>}:
  match b:
    case True{}:
      e
    case False{}:
      bt.absurd_some({rest == None{} : Maybe<&2, B.Dim>}, d, e)

# an ask of x that lacks nothing of f: x is within f in each dimension
def bt.fit_at(d: B.Dim, x: B.Amt, f: B.Amt, +now: Nat, +nm: Nat, +u: Nat, e: {B.lack(B.Ask{x, nm}, f, now, u) == None{} : Maybe<&2, B.Dim>}) -> {Nat.is_le(S.at(d, x), S.at(d, f)) == True{} : Bool}:
  match d:
    case B.Cost{}:
      match x f:
        case B.Amt{+xc, +xk, +xn, +xr} B.Amt{+fc, +fk, +fn, +fr}:
          bt.ok(Nat.is_le(xc, fc), B.Cost{}, B.lack.at(Nat.is_le(xk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), u), B.Time{}, B.lack.at(Nat.is_le(xn, fn), B.Calls{}, B.lack.at(Nat.is_le(xr, fr), B.Reqs{}, None{})))), e)
    case B.Tok{}:
      match x f:
        case B.Amt{+xc, +xk, +xn, +xr} B.Amt{+fc, +fk, +fn, +fr}:
          bt.ok(Nat.is_le(xk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), u), B.Time{}, B.lack.at(Nat.is_le(xn, fn), B.Calls{}, B.lack.at(Nat.is_le(xr, fr), B.Reqs{}, None{}))), bt.rest(Nat.is_le(xc, fc), B.Cost{}, B.lack.at(Nat.is_le(xk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), u), B.Time{}, B.lack.at(Nat.is_le(xn, fn), B.Calls{}, B.lack.at(Nat.is_le(xr, fr), B.Reqs{}, None{})))), e))
    case B.Time{}:
      {==}
    case B.Calls{}:
      match x f:
        case B.Amt{+xc, +xk, +xn, +xr} B.Amt{+fc, +fk, +fn, +fr}:
          bt.ok(Nat.is_le(xn, fn), B.Calls{}, B.lack.at(Nat.is_le(xr, fr), B.Reqs{}, None{}), bt.rest(Nat.is_le(Nat.add(now, nm), u), B.Time{}, B.lack.at(Nat.is_le(xn, fn), B.Calls{}, B.lack.at(Nat.is_le(xr, fr), B.Reqs{}, None{})), bt.rest(Nat.is_le(xk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), u), B.Time{}, B.lack.at(Nat.is_le(xn, fn), B.Calls{}, B.lack.at(Nat.is_le(xr, fr), B.Reqs{}, None{}))), bt.rest(Nat.is_le(xc, fc), B.Cost{}, B.lack.at(Nat.is_le(xk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), u), B.Time{}, B.lack.at(Nat.is_le(xn, fn), B.Calls{}, B.lack.at(Nat.is_le(xr, fr), B.Reqs{}, None{})))), e))))
    case B.Reqs{}:
      match x f:
        case B.Amt{+xc, +xk, +xn, +xr} B.Amt{+fc, +fk, +fn, +fr}:
          bt.ok(Nat.is_le(xr, fr), B.Reqs{}, None{}, bt.rest(Nat.is_le(xn, fn), B.Calls{}, B.lack.at(Nat.is_le(xr, fr), B.Reqs{}, None{}), bt.rest(Nat.is_le(Nat.add(now, nm), u), B.Time{}, B.lack.at(Nat.is_le(xn, fn), B.Calls{}, B.lack.at(Nat.is_le(xr, fr), B.Reqs{}, None{})), bt.rest(Nat.is_le(xk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), u), B.Time{}, B.lack.at(Nat.is_le(xn, fn), B.Calls{}, B.lack.at(Nat.is_le(xr, fr), B.Reqs{}, None{}))), bt.rest(Nat.is_le(xc, fc), B.Cost{}, B.lack.at(Nat.is_le(xk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), u), B.Time{}, B.lack.at(Nat.is_le(xn, fn), B.Calls{}, B.lack.at(Nat.is_le(xr, fr), B.Reqs{}, None{})))), e)))))

# an ask that lacks nothing: started now, its duration ends by the deadline
def bt.fit_time(x: B.Amt, f: B.Amt, +now: Nat, +nm: Nat, +u: Nat, e: {B.lack(B.Ask{x, nm}, f, now, u) == None{} : Maybe<&2, B.Dim>}) -> {Nat.is_le(Nat.add(now, nm), u) == True{} : Bool}:
  match x f:
    case B.Amt{+xc, +xk, +xn, +xr} B.Amt{+fc, +fk, +fn, +fr}:
      bt.ok(Nat.is_le(Nat.add(now, nm), u), B.Time{}, B.lack.at(Nat.is_le(xn, fn), B.Calls{}, B.lack.at(Nat.is_le(xr, fr), B.Reqs{}, None{})), bt.rest(Nat.is_le(xk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), u), B.Time{}, B.lack.at(Nat.is_le(xn, fn), B.Calls{}, B.lack.at(Nat.is_le(xr, fr), B.Reqs{}, None{}))), bt.rest(Nat.is_le(xc, fc), B.Cost{}, B.lack.at(Nat.is_le(xk, fk), B.Tok{}, B.lack.at(Nat.is_le(Nat.add(now, nm), u), B.Time{}, B.lack.at(Nat.is_le(xn, fn), B.Calls{}, B.lack.at(Nat.is_le(xr, fr), B.Reqs{}, None{})))), e)))

# an allotment w with the reserve b that lacks nothing: both are within
# what is free, in each dimension
def bt.fit_sum(+d: B.Dim, +w: B.Amt, +b: B.Amt, +f: B.Amt, +now: Nat, +nm: Nat, +u: Nat, +e: {B.lack(B.Ask{B.add4(w, b), nm}, f, now, u) == None{} : Maybe<&2, B.Dim>}) -> {Nat.is_le(Nat.add(S.at(d, w), S.at(d, b)), S.at(d, f)) == True{} : Bool}:
  %BS.bs.at_add4(d, w, b) : {Nat.is_le(_, S.at(d, f)) == True{} : Bool}
  bt.fit_at(d, B.add4(w, b), f, now, nm, u, e)

# then the allotment alone is within what is free
def bt.fit_le(+d: B.Dim, +w: B.Amt, +b: B.Amt, +f: B.Amt, +now: Nat, +nm: Nat, +u: Nat, +e: {B.lack(B.Ask{B.add4(w, b), nm}, f, now, u) == None{} : Maybe<&2, B.Dim>}) -> {Nat.is_le(S.at(d, w), S.at(d, f)) == True{} : Bool}:
  bt.le_add_l(S.at(d, w), S.at(d, b), S.at(d, f), bt.fit_sum(d, w, b, f, now, nm, u, e))

# the code's test of an amount is the spec's, whose reserve adds nothing
def bt.le_z(+w: Nat, +b: Nat, +f: Nat) -> {Nat.is_le(Nat.add(w, b), f) == Nat.is_le(Nat.add(w, Nat.add(b, 0n)), f) : Bool}:
  %Equal.sym(Nat, Nat.add(b, 0n), b, bt.add_zero(b)) : {Nat.is_le(Nat.add(w, b), f) == Nat.is_le(Nat.add(w, _), f) : Bool}
  {==}

# the code's test of the deadline is the spec's, whose reserve adds no time
def bt.time_z(+now: Nat, +wm: Nat, +bm: Nat, +u: Nat) -> {Nat.is_le(Nat.add(now, Nat.add(wm, bm)), u) == Nat.is_le(Nat.add(now, Nat.add(wm, Nat.add(bm, 0n))), u) : Bool}:
  %Equal.sym(Nat, Nat.add(bm, 0n), bm, bt.add_zero(bm)) : {Nat.is_le(Nat.add(now, Nat.add(wm, bm)), u) == Nat.is_le(Nat.add(now, Nat.add(wm, _)), u) : Bool}
  {==}

# five tests, each the same, are the same together
def bt.and5(-x1: Bool, -x2: Bool, -x3: Bool, -x4: Bool, -x5: Bool, -y1: Bool, -y2: Bool, -y3: Bool, -y4: Bool, -y5: Bool, e1: {x1 == y1 : Bool}, e2: {x2 == y2 : Bool}, e3: {x3 == y3 : Bool}, e4: {x4 == y4 : Bool}, e5: {x5 == y5 : Bool}) -> {Bool.and(x1, Bool.and(x2, Bool.and(x3, Bool.and(x4, x5)))) == Bool.and(y1, Bool.and(y2, Bool.and(y3, Bool.and(y4, y5)))) : Bool}:
  %e1 : {Bool.and(x1, Bool.and(x2, Bool.and(x3, Bool.and(x4, x5)))) == Bool.and(_, Bool.and(y2, Bool.and(y3, Bool.and(y4, y5)))) : Bool}
  %e2 : {Bool.and(x1, Bool.and(x2, Bool.and(x3, Bool.and(x4, x5)))) == Bool.and(x1, Bool.and(_, Bool.and(y3, Bool.and(y4, y5)))) : Bool}
  %e3 : {Bool.and(x1, Bool.and(x2, Bool.and(x3, Bool.and(x4, x5)))) == Bool.and(x1, Bool.and(x2, Bool.and(_, Bool.and(y4, y5)))) : Bool}
  %e4 : {Bool.and(x1, Bool.and(x2, Bool.and(x3, Bool.and(x4, x5)))) == Bool.and(x1, Bool.and(x2, Bool.and(x3, Bool.and(_, y5)))) : Bool}
  %e5 : {Bool.and(x1, Bool.and(x2, Bool.and(x3, Bool.and(x4, x5)))) == Bool.and(x1, Bool.and(x2, Bool.and(x3, Bool.and(x4, _)))) : Bool}
  {==}

# Carve
# -----

# a carve is answered exactly when the five tests hold
def bt.carved5(b1: Bool, b2: Bool, b3: Bool, b4: Bool, b5: Bool, -now: Nat, -wx: B.Amt, -wm: Nat, -f: B.Amt, -s: B.Amt, -l: B.Amt, -o: B.Amt, -h: List<&2, B.Hold>, -u: Nat) -> {S.carved(B.carve.fit(B.lack.at(b1, B.Cost{}, B.lack.at(b2, B.Tok{}, B.lack.at(b3, B.Time{}, B.lack.at(b4, B.Calls{}, B.lack.at(b5, B.Reqs{}, None{}))))), now, B.Ask{wx, wm}, f, s, l, o, h, u)) == Bool.and(b1, Bool.and(b2, Bool.and(b3, Bool.and(b4, b5)))) : Bool}:
  match b1:
    case True{}:
      match b2:
        case True{}:
          match b3:
            case True{}:
              match b4:
                case True{}:
                  match b5:
                    case True{}:
                      {==}
                    case False{}:
                      {==}
                case False{}:
                  {==}
            case False{}:
              {==}
        case False{}:
          {==}
    case False{}:
      {==}

# a Working account carves exactly when the allotment with the reserves
# above fits what is free by the deadline
def bt.carve_iff_w(wx: B.Amt, bx: B.Amt, f: B.Amt, +now: Nat, +wm: Nat, +bm: Nat, -s: B.Amt, -l: B.Amt, -o: B.Amt, -h: List<&2, B.Hold>, +u: Nat) -> {S.carved(B.carve.fit(B.lack(B.need(B.Final{}, B.Ask{bx, bm}, B.Ask{B.zero(), 0n}, B.Ask{wx, wm}), f, now, u), now, B.Ask{wx, wm}, f, s, l, o, h, u)) == S.fits(B.Final{}, B.Ask{bx, bm}, S.nothing(), B.Ask{wx, wm}, f, now, u) : Bool}:
  match wx bx f:
    case B.Amt{+wc, +wk, +wn, +wr} B.Amt{+bc, +bk, +bn, +br} B.Amt{+fc, +fk, +fn, +fr}:
      %bt.and5(Nat.is_le(Nat.add(wc, bc), fc), Nat.is_le(Nat.add(wk, bk), fk), Nat.is_le(Nat.add(now, Nat.add(wm, bm)), u), Nat.is_le(Nat.add(wn, bn), fn), Nat.is_le(Nat.add(wr, br), fr), Nat.is_le(Nat.add(wc, Nat.add(bc, 0n)), fc), Nat.is_le(Nat.add(wk, Nat.add(bk, 0n)), fk), Nat.is_le(Nat.add(now, Nat.add(wm, Nat.add(bm, 0n))), u), Nat.is_le(Nat.add(wn, Nat.add(bn, 0n)), fn), Nat.is_le(Nat.add(wr, Nat.add(br, 0n)), fr), bt.le_z(wc, bc, fc), bt.le_z(wk, bk, fk), bt.time_z(now, wm, bm, u), bt.le_z(wn, bn, fn), bt.le_z(wr, br, fr)) : {S.carved(B.carve.fit(B.lack(B.Ask{B.Amt{Nat.add(wc, bc), Nat.add(wk, bk), Nat.add(wn, bn), Nat.add(wr, br)}, Nat.add(wm, bm)}, B.Amt{fc, fk, fn, fr}, now, u), now, B.Ask{B.Amt{wc, wk, wn, wr}, wm}, B.Amt{fc, fk, fn, fr}, s, l, o, h, u)) == _ : Bool}
      bt.carved5(Nat.is_le(Nat.add(wc, bc), fc), Nat.is_le(Nat.add(wk, bk), fk), Nat.is_le(Nat.add(now, Nat.add(wm, bm)), u), Nat.is_le(Nat.add(wn, bn), fn), Nat.is_le(Nat.add(wr, br), fr), now, B.Amt{wc, wk, wn, wr}, wm, B.Amt{fc, fk, fn, fr}, s, l, o, h, u)

def bt.carve_iff(ph: B.Phase, +now: Nat, want: B.Ask, base: B.Ask, a: B.Acct) -> {S.carved(B.carve(ph, now, want, base, a)) == Bool.and(S.working(ph), S.fits(B.Final{}, base, S.nothing(), want, S.free(a), now, S.until(a))) : Bool}:
  match ph:
    case B.Working{}:
      match want base a:
        case B.Ask{wx, +wm} B.Ask{bx, +bm} B.Acct{f, s, l, o, h, +u}:
          bt.carve_iff_w(wx, bx, f, now, wm, bm, s, l, o, h, u)
    case B.WrapUp{}:
      {==}
    case B.Exhausted{}:
      {==}

# what budget_carve_moves says of the answer r to a carve of want, with
# the reserves base, at now off a
def bt.Moves(+now: Nat, +want: B.Ask, +base: B.Ask, +a: B.Acct, +d: B.Dim, r: B.Carve) -> Type:
  match r:
    case B.Carved{+p, +c}:
      {Nat.add(S.at(d, S.free(p)), S.at(d, S.amt(want))) == S.at(d, S.free(a)) : Nat} & {S.at(d, S.lent(p)) == Nat.add(S.at(d, S.lent(a)), S.at(d, S.amt(want))) : Nat} & {Nat.is_le(S.at(d, S.amt(base)), S.at(d, S.free(p))) == True{} : Bool} & {S.spent(p) == S.spent(a) : B.Amt} & {S.over(p) == S.over(a) : B.Amt} & {S.holds(p) == S.holds(a) : List<&2, B.Hold>} & {S.until(p) == S.until(a) : Nat} & {c == B.Acct{S.amt(want), B.Amt{0n, 0n, 0n, 0n}, B.Amt{0n, 0n, 0n, 0n}, B.Amt{0n, 0n, 0n, 0n}, Nil{}, Nat.add(now, S.ms(want))} : B.Acct} & {Nat.is_le(Nat.add(Nat.add(now, S.ms(want)), S.ms(base)), S.until(a)) == True{} : Bool}
    case B.Kept{w}:
      Unit

# what is left free and the allotment are what was free
def bt.mv_free(+d: B.Dim, +f: B.Amt, +w: B.Amt, +le: {Nat.is_le(S.at(d, w), S.at(d, f)) == True{} : Bool}) -> {Nat.add(S.at(d, B.sub4(f, w)), S.at(d, w)) == S.at(d, f) : Nat}:
  %Equal.sym(Nat, S.at(d, B.sub4(f, w)), Nat.sub(S.at(d, f), S.at(d, w)), BS.bs.at_sub4(d, f, w)) : {Nat.add(_, S.at(d, w)) == S.at(d, f) : Nat}
  bt.add_sub(S.at(d, w), S.at(d, f), le)

# the reserves are within what is left free
def bt.mv_keep(+d: B.Dim, +w: B.Amt, +b: B.Amt, +f: B.Amt, +fit: {Nat.is_le(Nat.add(S.at(d, w), S.at(d, b)), S.at(d, f)) == True{} : Bool}) -> {Nat.is_le(S.at(d, b), S.at(d, B.sub4(f, w))) == True{} : Bool}:
  %Equal.sym(Nat, S.at(d, B.sub4(f, w)), Nat.sub(S.at(d, f), S.at(d, w)), BS.bs.at_sub4(d, f, w)) : {Nat.is_le(S.at(d, b), _) == True{} : Bool}
  bt.le_sub(S.at(d, w), S.at(d, b), S.at(d, f), fit)

# the child's deadline and the reserves' durations end by the parent's
def bt.mv_time(+now: Nat, +wm: Nat, +bm: Nat, +u: Nat, e: {Nat.is_le(Nat.add(now, Nat.add(wm, bm)), u) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.add(now, wm), bm), u) == True{} : Bool}:
  %Equal.sym(Nat, Nat.add(Nat.add(now, wm), bm), Nat.add(now, Nat.add(wm, bm)), bt.add_assoc(now, wm, bm)) : {Nat.is_le(_, u) == True{} : Bool}
  e

def bt.moves_fit(m: Maybe<&2, B.Dim>, +now: Nat, +wx: B.Amt, +wm: Nat, +bx: B.Amt, +bm: Nat, +f: B.Amt, -s: B.Amt, +l: B.Amt, -o: B.Amt, -h: List<&2, B.Hold>, +u: Nat, +d: B.Dim, +e: {B.lack(B.need(B.Final{}, B.Ask{bx, bm}, B.Ask{B.zero(), 0n}, B.Ask{wx, wm}), f, now, u) == m : Maybe<&2, B.Dim>}) -> bt.Moves(now, B.Ask{wx, wm}, B.Ask{bx, bm}, B.Acct{f, s, l, o, h, u}, d, B.carve.fit(m, now, B.Ask{wx, wm}, f, s, l, o, h, u)):
  match m:
    case None{}:
      (bt.mv_free(d, f, wx, bt.fit_le(d, wx, bx, f, now, Nat.add(wm, bm), u, e)), (BS.bs.at_add4(d, l, wx), (bt.mv_keep(d, wx, bx, f, bt.fit_sum(d, wx, bx, f, now, Nat.add(wm, bm), u, e)), ({==}, ({==}, ({==}, ({==}, ({==}, bt.mv_time(now, wm, bm, u, bt.fit_time(B.add4(wx, bx), f, now, Nat.add(wm, bm), u, e))))))))))
    case Some{x}:
      Unit{}

def bt.moves(ph: B.Phase, +now: Nat, want: B.Ask, base: B.Ask, a: B.Acct, +d: B.Dim) -> bt.Moves(now, want, base, a, d, B.carve(ph, now, want, base, a)):
  match ph:
    case B.Working{}:
      match want base a:
        case B.Ask{+wx, +wm} B.Ask{+bx, +bm} B.Acct{+f, s, +l, o, h, +u}:
          bt.moves_fit(B.lack(B.need(B.Final{}, B.Ask{bx, bm}, B.Ask{B.zero(), 0n}, B.Ask{wx, wm}), f, now, u), now, wx, wm, bx, bm, f, s, l, o, h, u, d, {==})
    case B.WrapUp{}:
      Unit{}
    case B.Exhausted{}:
      Unit{}

# Close
# -----

# a close is answered exactly when the child is idle
def bt.closed_idle(b: Bool, -cf: B.Amt, -cs: B.Amt, -co: B.Amt, -pf: B.Amt, -ps: B.Amt, -pl: B.Amt, -po: B.Amt, -ph: List<&2, B.Hold>, -pu: Nat) -> {S.closed(B.close.idle(b, cf, cs, co, pf, ps, pl, po, ph, pu)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the code's idle test is the spec's
def bt.idle_eq(ch: List<&2, B.Hold>, +cl: B.Amt) -> {Bool.and(B.close.holds(ch), B.is_zero4(cl)) == Bool.and(S.no_holds(ch), S.none4(cl)) : Bool}:
  match ch:
    case Nil{}:
      bt.zero_none(cl)
    case Con{x, t}:
      {==}

def bt.close_iff(c: B.Acct, p: B.Acct) -> {S.closed(B.close(c, p)) == S.idle(c) : Bool}:
  match c p:
    case B.Acct{cf, cs, +cl, co, +ch, cu} B.Acct{pf, ps, pl, po, ph, pu}:
      %bt.idle_eq(ch, cl) : {S.closed(B.close.idle(Bool.and(B.close.holds(ch), B.is_zero4(cl)), cf, cs, co, pf, ps, pl, po, ph, pu)) == _ : Bool}
      bt.closed_idle(Bool.and(B.close.holds(ch), B.is_zero4(cl)), cf, cs, co, pf, ps, pl, po, ph, pu)

# what budget_close_returns says of the answer r to a close of a child with
# cf free and cs spent into p
def bt.Returns(+p: B.Acct, +cf: B.Amt, +cs: B.Amt, +d: B.Dim, r: B.Close) -> Type:
  match r:
    case B.Closed{+p2, c2}:
      {S.at(d, S.free(p2)) == Nat.add(S.at(d, S.free(p)), S.at(d, cf)) : Nat} & {S.at(d, S.spent(p2)) == Nat.add(S.at(d, S.spent(p)), S.at(d, cs)) : Nat} & {S.at(d, S.lent(p2)) == Nat.sub(S.at(d, S.lent(p)), Nat.add(S.at(d, cf), S.at(d, cs))) : Nat} & {S.at(d, S.over(p2)) == S.at(d, S.over(p)) : Nat} & {S.holds(p2) == S.holds(p) : List<&2, B.Hold>} & {S.until(p2) == S.until(p) : Nat} & {c2 == S.empty() : B.Acct}
    case B.Busy{}:
      Unit

# less nothing of z in dimension d is all of x
def bt.at_sub_clean(+d: B.Dim, +x: B.Amt, +z: B.Amt, clean: {S.at(d, z) == 0n : Nat}) -> {S.at(d, B.sub4(x, z)) == S.at(d, x) : Nat}:
  %bt.sub_zero(S.at(d, x)) : {S.at(d, B.sub4(x, z)) == _ : Nat}
  %clean : {S.at(d, B.sub4(x, z)) == Nat.sub(S.at(d, x), _) : Nat}
  BS.bs.at_sub4(d, x, z)

# nothing of z past y in dimension d adds nothing to o
def bt.at_add_clean(+d: B.Dim, +o: B.Amt, +z: B.Amt, +y: B.Amt, clean: {S.at(d, z) == 0n : Nat}) -> {S.at(d, B.add4(o, B.sub4(z, y))) == S.at(d, o) : Nat}:
  %bt.add_zero(S.at(d, o)) : {S.at(d, B.add4(o, B.sub4(z, y))) == _ : Nat}
  %clean : {S.at(d, B.add4(o, B.sub4(z, y))) == Nat.add(S.at(d, o), Nat.sub(_, S.at(d, y))) : Nat}
  %BS.bs.at_sub4(d, z, y) : {S.at(d, B.add4(o, B.sub4(z, y))) == Nat.add(S.at(d, o), _) : Nat}
  BS.bs.at_add4(d, o, B.sub4(z, y))

# the parent's free and the child's
def bt.ret_free(+d: B.Dim, +pf: B.Amt, +cf: B.Amt, +co: B.Amt, clean: {S.at(d, co) == 0n : Nat}) -> {S.at(d, B.sub4(B.add4(pf, cf), co)) == Nat.add(S.at(d, pf), S.at(d, cf)) : Nat}:
  %BS.bs.at_add4(d, pf, cf) : {S.at(d, B.sub4(B.add4(pf, cf), co)) == _ : Nat}
  bt.at_sub_clean(d, B.add4(pf, cf), co, clean)

# what was lent less the child's free and spend
def bt.ret_lent(+d: B.Dim, +pl: B.Amt, +cf: B.Amt, +cs: B.Amt, +co: B.Amt, clean: {S.at(d, co) == 0n : Nat}) -> {S.at(d, B.sub4(pl, B.sub4(B.add4(cf, cs), co))) == Nat.sub(S.at(d, pl), Nat.add(S.at(d, cf), S.at(d, cs))) : Nat}:
  %BS.bs.at_add4(d, cf, cs) : {S.at(d, B.sub4(pl, B.sub4(B.add4(cf, cs), co))) == Nat.sub(S.at(d, pl), _) : Nat}
  %bt.at_sub_clean(d, B.add4(cf, cs), co, clean) : {S.at(d, B.sub4(pl, B.sub4(B.add4(cf, cs), co))) == Nat.sub(S.at(d, pl), _) : Nat}
  BS.bs.at_sub4(d, pl, B.sub4(B.add4(cf, cs), co))

def bt.returns_idle(b: Bool, +cf: B.Amt, +cs: B.Amt, +co: B.Amt, +pf: B.Amt, +ps: B.Amt, +pl: B.Amt, +po: B.Amt, -ph: List<&2, B.Hold>, -pu: Nat, +d: B.Dim, +clean: {S.at(d, co) == 0n : Nat}) -> bt.Returns(B.Acct{pf, ps, pl, po, ph, pu}, cf, cs, d, B.close.idle(b, cf, cs, co, pf, ps, pl, po, ph, pu)):
  match b:
    case True{}:
      (bt.ret_free(d, pf, cf, co, clean), (BS.bs.at_add4(d, ps, cs), (bt.ret_lent(d, pl, cf, cs, co, clean), (bt.at_add_clean(d, po, co, B.add4(pf, cf), clean), ({==}, ({==}, {==}))))))
    case False{}:
      Unit{}

def bt.returns(c: B.Acct, p: B.Acct, +d: B.Dim, +clean: {S.at(d, S.over(c)) == 0n : Nat}) -> bt.Returns(p, S.free(c), S.spent(c), d, B.close(c, p)):
  match c p:
    case B.Acct{+cf, +cs, cl, +co, ch, cu} B.Acct{+pf, +ps, +pl, +po, ph, pu}:
      bt.returns_idle(Bool.and(B.close.holds(ch), B.is_zero4(cl)), cf, cs, co, pf, ps, pl, po, ph, pu, d, clean)

# what budget_close_conserves says of the answer r to a close into p
def bt.Conserves(+p: B.Acct, +d: B.Dim, r: B.Close) -> Type:
  match r:
    case B.Closed{+p2, c2}:
      {Nat.add(S.net(d, p2), S.at(d, S.over(p))) == Nat.add(S.net(d, p), S.at(d, S.over(p2))) : Nat}
    case B.Busy{}:
      Unit

# (x + y) - z in dimension d
def bt.at1(+d: B.Dim, +x: B.Amt, +y: B.Amt, +z: B.Amt) -> {Nat.sub(Nat.add(S.at(d, x), S.at(d, y)), S.at(d, z)) == S.at(d, B.sub4(B.add4(x, y), z)) : Nat}:
  %BS.bs.at_add4(d, x, y) : {Nat.sub(_, S.at(d, z)) == S.at(d, B.sub4(B.add4(x, y), z)) : Nat}
  %BS.bs.at_sub4(d, B.add4(x, y), z) : {_ == S.at(d, B.sub4(B.add4(x, y), z)) : Nat}
  {==}

# x + y in dimension d
def bt.at2(+d: B.Dim, +x: B.Amt, +y: B.Amt) -> {Nat.add(S.at(d, x), S.at(d, y)) == S.at(d, B.add4(x, y)) : Nat}:
  Equal.sym(Nat, S.at(d, B.add4(x, y)), Nat.add(S.at(d, x), S.at(d, y)), BS.bs.at_add4(d, x, y))

# l - ((x + y) - z) in dimension d
def bt.at3(+d: B.Dim, +l: B.Amt, +x: B.Amt, +y: B.Amt, +z: B.Amt) -> {Nat.sub(S.at(d, l), Nat.sub(Nat.add(S.at(d, x), S.at(d, y)), S.at(d, z))) == S.at(d, B.sub4(l, B.sub4(B.add4(x, y), z))) : Nat}:
  %BS.bs.at_add4(d, x, y) : {Nat.sub(S.at(d, l), Nat.sub(_, S.at(d, z))) == S.at(d, B.sub4(l, B.sub4(B.add4(x, y), z))) : Nat}
  %BS.bs.at_sub4(d, B.add4(x, y), z) : {Nat.sub(S.at(d, l), _) == S.at(d, B.sub4(l, B.sub4(B.add4(x, y), z))) : Nat}
  %BS.bs.at_sub4(d, l, B.sub4(B.add4(x, y), z)) : {_ == S.at(d, B.sub4(l, B.sub4(B.add4(x, y), z))) : Nat}
  {==}

# o + (z - (x + y)) in dimension d
def bt.at4(+d: B.Dim, +o: B.Amt, +z: B.Amt, +x: B.Amt, +y: B.Amt) -> {Nat.add(S.at(d, o), Nat.sub(S.at(d, z), Nat.add(S.at(d, x), S.at(d, y)))) == S.at(d, B.add4(o, B.sub4(z, B.add4(x, y)))) : Nat}:
  %BS.bs.at_add4(d, x, y) : {Nat.add(S.at(d, o), Nat.sub(S.at(d, z), _)) == S.at(d, B.add4(o, B.sub4(z, B.add4(x, y)))) : Nat}
  %BS.bs.at_sub4(d, z, B.add4(x, y)) : {Nat.add(S.at(d, o), _) == S.at(d, B.add4(o, B.sub4(z, B.add4(x, y)))) : Nat}
  %BS.bs.at_add4(d, o, B.sub4(z, B.add4(x, y))) : {_ == S.at(d, B.add4(o, B.sub4(z, B.add4(x, y)))) : Nat}
  {==}

# the conservation of numbers is the conservation of the amounts' dimension
def bt.conserve_eq(-n1: Nat, -a1: Nat, -n2: Nat, -a2: Nat, -n3: Nat, -a3: Nat, -n4: Nat, -a4: Nat, -hh: Nat, -po: Nat, -base: Nat, e1: {n1 == a1 : Nat}, e2: {n2 == a2 : Nat}, e3: {n3 == a3 : Nat}, e4: {n4 == a4 : Nat}, h: {Nat.add(Nat.add(n1, Nat.add(hh, Nat.add(n2, n3))), po) == Nat.add(base, n4) : Nat}) -> {Nat.add(Nat.add(a1, Nat.add(hh, Nat.add(a2, a3))), po) == Nat.add(base, a4) : Nat}:
  %e1 : {Nat.add(Nat.add(_, Nat.add(hh, Nat.add(a2, a3))), po) == Nat.add(base, a4) : Nat}
  %e2 : {Nat.add(Nat.add(n1, Nat.add(hh, Nat.add(_, a3))), po) == Nat.add(base, a4) : Nat}
  %e3 : {Nat.add(Nat.add(n1, Nat.add(hh, Nat.add(n2, _))), po) == Nat.add(base, a4) : Nat}
  %e4 : {Nat.add(Nat.add(n1, Nat.add(hh, Nat.add(n2, n3))), po) == Nat.add(base, _) : Nat}
  h

def bt.conserves_idle(b: Bool, +cf: B.Amt, +cs: B.Amt, +co: B.Amt, +pf: B.Amt, +ps: B.Amt, +pl: B.Amt, +po: B.Amt, +ph: List<&2, B.Hold>, -pu: Nat, +d: B.Dim, +funded: {Nat.is_le(S.at(d, co), Nat.add(S.at(d, cf), S.at(d, cs))) == True{} : Bool}, +ours: {Nat.is_le(Nat.sub(Nat.add(S.at(d, cf), S.at(d, cs)), S.at(d, co)), S.at(d, pl)) == True{} : Bool}) -> bt.Conserves(B.Acct{pf, ps, pl, po, ph, pu}, d, B.close.idle(b, cf, cs, co, pf, ps, pl, po, ph, pu)):
  match b:
    case True{}:
      bt.conserve_eq(Nat.sub(Nat.add(S.at(d, pf), S.at(d, cf)), S.at(d, co)), S.at(d, B.sub4(B.add4(pf, cf), co)), Nat.add(S.at(d, ps), S.at(d, cs)), S.at(d, B.add4(ps, cs)), Nat.sub(S.at(d, pl), Nat.sub(Nat.add(S.at(d, cf), S.at(d, cs)), S.at(d, co))), S.at(d, B.sub4(pl, B.sub4(B.add4(cf, cs), co))), Nat.add(S.at(d, po), Nat.sub(S.at(d, co), Nat.add(S.at(d, pf), S.at(d, cf)))), S.at(d, B.add4(po, B.sub4(co, B.add4(pf, cf)))), S.held(d, ph), S.at(d, po), Nat.add(S.at(d, pf), Nat.add(S.held(d, ph), Nat.add(S.at(d, ps), S.at(d, pl)))), bt.at1(d, pf, cf, co), bt.at2(d, ps, cs), bt.at3(d, pl, cf, cs, co), bt.at4(d, po, co, pf, cf), bt.conserve(S.at(d, pf), S.at(d, cf), S.at(d, cs), S.at(d, co), S.at(d, ps), S.at(d, pl), S.at(d, po), S.held(d, ph), funded, ours))
    case False{}:
      Unit{}

def bt.conserves(c: B.Acct, p: B.Acct, +d: B.Dim, +funded: {Nat.is_le(S.at(d, S.over(c)), Nat.add(S.at(d, S.free(c)), S.at(d, S.spent(c)))) == True{} : Bool}, +ours: {Nat.is_le(Nat.sub(Nat.add(S.at(d, S.free(c)), S.at(d, S.spent(c))), S.at(d, S.over(c))), S.at(d, S.lent(p))) == True{} : Bool}) -> bt.Conserves(p, d, B.close(c, p)):
  match c p:
    case B.Acct{+cf, +cs, cl, +co, ch, cu} B.Acct{+pf, +ps, +pl, +po, +ph, pu}:
      bt.conserves_idle(Bool.and(B.close.holds(ch), B.is_zero4(cl)), cf, cs, co, pf, ps, pl, po, ph, pu, d, funded, ours)

# Carve, then close
# -----------------

def bt.closed_eq(-f1: B.Amt, -f2: B.Amt, -s1: B.Amt, -s2: B.Amt, -l1: B.Amt, -l2: B.Amt, -o1: B.Amt, -o2: B.Amt, -h: List<&2, B.Hold>, -u: Nat, -k: B.Acct, ef: {f1 == f2 : B.Amt}, es: {s1 == s2 : B.Amt}, el: {l1 == l2 : B.Amt}, eo: {o1 == o2 : B.Amt}) -> {B.Closed{B.Acct{f1, s1, l1, o1, h, u}, k} == B.Closed{B.Acct{f2, s2, l2, o2, h, u}, k} : B.Close}:
  %ef : {B.Closed{B.Acct{f1, s1, l1, o1, h, u}, k} == B.Closed{B.Acct{_, s2, l2, o2, h, u}, k} : B.Close}
  %es : {B.Closed{B.Acct{f1, s1, l1, o1, h, u}, k} == B.Closed{B.Acct{f1, _, l2, o2, h, u}, k} : B.Close}
  %el : {B.Closed{B.Acct{f1, s1, l1, o1, h, u}, k} == B.Closed{B.Acct{f1, s1, _, o2, h, u}, k} : B.Close}
  %eo : {B.Closed{B.Acct{f1, s1, l1, o1, h, u}, k} == B.Closed{B.Acct{f1, s1, l1, _, h, u}, k} : B.Close}
  {==}

# what budget_carve_close_round_trip says of the answer r to a carve off a
def bt.Round(+a: B.Acct, r: B.Carve) -> Type:
  match r:
    case B.Carved{p, c}:
      {B.close(c, p) == B.Closed{a, S.empty()} : B.Close}
    case B.Kept{w}:
      Unit

def bt.round_fit(m: Maybe<&2, B.Dim>, +now: Nat, +wx: B.Amt, +wm: Nat, +bx: B.Amt, +bm: Nat, +f: B.Amt, +s: B.Amt, +l: B.Amt, +o: B.Amt, -h: List<&2, B.Hold>, +u: Nat, +e: {B.lack(B.need(B.Final{}, B.Ask{bx, bm}, B.Ask{B.zero(), 0n}, B.Ask{wx, wm}), f, now, u) == m : Maybe<&2, B.Dim>}) -> bt.Round(B.Acct{f, s, l, o, h, u}, B.carve.fit(m, now, B.Ask{wx, wm}, f, s, l, o, h, u)):
  match m:
    case None{}:
      bt.closed_eq(B.sub4(B.add4(B.sub4(f, wx), wx), B.zero()), f, B.add4(s, B.zero()), s, B.sub4(B.add4(l, wx), B.sub4(B.add4(wx, B.zero()), B.zero())), l, B.add4(o, B.sub4(B.zero(), B.add4(B.sub4(f, wx), wx))), o, h, u, S.empty(), bt.give_back(f, wx, bt.fit_le(B.Cost{}, wx, bx, f, now, Nat.add(wm, bm), u, e), bt.fit_le(B.Tok{}, wx, bx, f, now, Nat.add(wm, bm), u, e), bt.fit_le(B.Calls{}, wx, bx, f, now, Nat.add(wm, bm), u, e), bt.fit_le(B.Reqs{}, wx, bx, f, now, Nat.add(wm, bm), u, e)), bt.add4_zero(s), bt.lent_back(l, wx), bt.over_back(o, B.add4(B.sub4(f, wx), wx)))
    case Some{x}:
      Unit{}

def bt.round(ph: B.Phase, +now: Nat, want: B.Ask, base: B.Ask, a: B.Acct) -> bt.Round(a, B.carve(ph, now, want, base, a)):
  match ph:
    case B.Working{}:
      match want base a:
        case B.Ask{+wx, +wm} B.Ask{+bx, +bm} B.Acct{+f, +s, +l, +o, h, +u}:
          bt.round_fit(B.lack(B.need(B.Final{}, B.Ask{bx, bm}, B.Ask{B.zero(), 0n}, B.Ask{wx, wm}), f, now, u), now, wx, wm, bx, bm, f, s, l, o, h, u, {==})
    case B.WrapUp{}:
      Unit{}
    case B.Exhausted{}:
      Unit{}

# Why a carve is kept
# -------------------

# a Working agent's carve is carved or kept short
def bt.either_fit(m: Maybe<&2, B.Dim>, -now: Nat, -wx: B.Amt, -wm: Nat, -f: B.Amt, -s: B.Amt, -l: B.Amt, -o: B.Amt, -h: List<&2, B.Hold>, -u: Nat) -> {Bool.or(S.carved(B.carve.fit(m, now, B.Ask{wx, wm}, f, s, l, o, h, u)), S.kept_short(B.carve.fit(m, now, B.Ask{wx, wm}, f, s, l, o, h, u))) == True{} : Bool}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def bt.either(+now: Nat, want: B.Ask, base: B.Ask, a: B.Acct) -> {Bool.or(S.carved(B.carve(B.Working{}, now, want, base, a)), S.kept_short(B.carve(B.Working{}, now, want, base, a))) == True{} : Bool}:
  match want base a:
    case B.Ask{+wx, +wm} B.Ask{+bx, +bm} B.Acct{+f, s, l, o, h, +u}:
      bt.either_fit(B.lack(B.need(B.Final{}, B.Ask{bx, bm}, B.Ask{B.zero(), 0n}, B.Ask{wx, wm}), f, now, u), now, wx, wm, f, s, l, o, h, u)

# a Working agent's carve that does not fit is kept short
def bt.kept_why(+now: Nat, +want: B.Ask, +base: B.Ask, +a: B.Acct) -> {Bool.or(S.fits(B.Final{}, base, S.nothing(), want, S.free(a), now, S.until(a)), S.kept_short(B.carve(B.Working{}, now, want, base, a))) == True{} : Bool}:
  %bt.carve_iff(B.Working{}, now, want, base, a) : {Bool.or(_, S.kept_short(B.carve(B.Working{}, now, want, base, a))) == True{} : Bool}
  bt.either(now, want, base, a)

# a carve answered Kept proves the goal G; one answered Carved, nothing
def bt.IfKept(c: B.Carve, G: Type) -> Type:
  match c:
    case B.Carved{p, k}:
      Unit
    case B.Kept{w}:
      G

# the dimension a carve is kept short for, x for any other answer
def bt.kept_dim(c: B.Carve, x: B.Dim) -> B.Dim:
  match c:
    case B.Carved{p, k}:
      x
    case B.Kept{w}:
      match w:
        case B.Short{e}:
          e
        case B.Held{}:
          x
        case B.Stopped{}:
          x

# a carve kept short for d by the code's lack m: m names d, and the
# dimension m names fails the spec's test (br.lack_ok)
def bt.short_fit(m: Maybe<&2, B.Dim>, +now: Nat, +wx: B.Amt, +wm: Nat, +bx: B.Amt, +bm: Nat, +f: B.Amt, -s: B.Amt, -l: B.Amt, -o: B.Amt, -h: List<&2, B.Hold>, +u: Nat, +d: B.Dim, lo: BR.br.LackOk(m, B.Final{}, B.Ask{bx, bm}, S.nothing(), B.Ask{wx, wm}, f, now, u), g: {B.carve.fit(m, now, B.Ask{wx, wm}, f, s, l, o, h, u) == B.Kept{B.Short{d}} : B.Carve}) -> {S.short_in(B.Final{}, B.Ask{bx, bm}, S.nothing(), B.Ask{wx, wm}, f, now, u, d) == True{} : Bool}:
  match m:
    case None{}:
      %g : bt.IfKept(_, {S.short_in(B.Final{}, B.Ask{bx, bm}, S.nothing(), B.Ask{wx, wm}, f, now, u, d) == True{} : Bool})
      Unit{}
    case Some{+x}:
      (nf, ns) = lo
      %g : {S.short_in(B.Final{}, B.Ask{bx, bm}, S.nothing(), B.Ask{wx, wm}, f, now, u, bt.kept_dim(_, d)) == True{} : Bool}
      BR.br.short_of(x, B.Final{}, B.Ask{bx, bm}, S.nothing(), B.Ask{wx, wm}, f, now, u, ns)

# a Working agent's carve kept short names a dimension the spec calls
# short
def bt.kept_short(+now: Nat, want: B.Ask, base: B.Ask, a: B.Acct, +d: B.Dim, g: {B.carve(B.Working{}, now, want, base, a) == B.Kept{B.Short{d}} : B.Carve}) -> {S.short_in(B.Final{}, base, S.nothing(), want, S.free(a), now, S.until(a), d) == True{} : Bool}:
  match want base a:
    case B.Ask{+wx, +wm} B.Ask{+bx, +bm} B.Acct{+f, s, l, o, h, +u}:
      bt.short_fit(B.lack(B.need(B.Final{}, B.Ask{bx, bm}, S.nothing(), B.Ask{wx, wm}), f, now, u), now, wx, wm, bx, bm, f, s, l, o, h, u, d, BR.br.lack_ok(B.Final{}, B.Ask{bx, bm}, S.nothing(), B.Ask{wx, wm}, f, now, u), g)

# Close of an overrun
# -------------------

# what budget_close_takes_overrun says of the answer r to a close of a
# child with cf free, cs spent and the overrun co into p
def bt.Takes(+p: B.Acct, +cf: B.Amt, +cs: B.Amt, +co: B.Amt, +d: B.Dim, r: B.Close) -> Type:
  match r:
    case B.Closed{+p2, c2}:
      {S.at(d, S.free(p2)) == Nat.sub(Nat.add(S.at(d, S.free(p)), S.at(d, cf)), S.at(d, co)) : Nat} & {S.at(d, S.over(p2)) == Nat.add(S.at(d, S.over(p)), Nat.sub(S.at(d, co), Nat.add(S.at(d, S.free(p)), S.at(d, cf)))) : Nat} & {S.at(d, S.spent(p2)) == Nat.add(S.at(d, S.spent(p)), S.at(d, cs)) : Nat} & {S.holds(p2) == S.holds(p) : List<&2, B.Hold>} & {S.until(p2) == S.until(p) : Nat} & {c2 == S.empty() : B.Acct}
    case B.Busy{}:
      Unit

def bt.takes_idle(b: Bool, +cf: B.Amt, +cs: B.Amt, +co: B.Amt, +pf: B.Amt, +ps: B.Amt, -pl: B.Amt, +po: B.Amt, -ph: List<&2, B.Hold>, -pu: Nat, +d: B.Dim) -> bt.Takes(B.Acct{pf, ps, pl, po, ph, pu}, cf, cs, co, d, B.close.idle(b, cf, cs, co, pf, ps, pl, po, ph, pu)):
  match b:
    case True{}:
      (Equal.sym(Nat, Nat.sub(Nat.add(S.at(d, pf), S.at(d, cf)), S.at(d, co)), S.at(d, B.sub4(B.add4(pf, cf), co)), bt.at1(d, pf, cf, co)), (Equal.sym(Nat, Nat.add(S.at(d, po), Nat.sub(S.at(d, co), Nat.add(S.at(d, pf), S.at(d, cf)))), S.at(d, B.add4(po, B.sub4(co, B.add4(pf, cf)))), bt.at4(d, po, co, pf, cf)), (BS.bs.at_add4(d, ps, cs), ({==}, ({==}, {==})))))
    case False{}:
      Unit{}

def bt.takes(c: B.Acct, p: B.Acct, +d: B.Dim) -> bt.Takes(p, S.free(c), S.spent(c), S.over(c), d, B.close(c, p)):
  match c p:
    case B.Acct{+cf, +cs, cl, +co, ch, cu} B.Acct{+pf, +ps, pl, +po, ph, pu}:
      bt.takes_idle(Bool.and(B.close.holds(ch), B.is_zero4(cl)), cf, cs, co, pf, ps, pl, po, ph, pu, d)
