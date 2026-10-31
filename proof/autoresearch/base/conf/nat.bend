# eukhe: natural-number lemmas for the proof of LAW confidence_exact
# (sums, products, differences, order, division by a positive number)

import Base

# Absurd cases
# ------------

def ac.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# False is not True
def ac.ft(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ac.BD(_, A, Unit)
  Unit{}

def ac.tf(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : ac.BD(_, Unit, A)
  Unit{}

# Sums
# ----

def ac.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %ac.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def ac.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %ac.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def ac.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, ac.add_zero(b))
    case 1n++p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), ac.add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %ac.add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def ac.add_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %ac.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def ac.add_assoc_r(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), ac.add_assoc(a, b, c))

# a + (b + c) = b + (a + c)
def ac.add_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  %ac.add_assoc(a, b, c) : {_ == Nat.add(b, Nat.add(a, c)) : Nat}
  %ac.add_comm(b, a) : {Nat.add(_, c) == Nat.add(b, Nat.add(a, c)) : Nat}
  ac.add_assoc(b, a, c)

# (a + b) + (c + d) = (a + c) + (b + d)
def ac.add_4(+a: Nat, +b: Nat, +c: Nat, +d: Nat) -> {Nat.add(Nat.add(a, b), Nat.add(c, d)) == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}:
  %ac.add_assoc_r(a, b, Nat.add(c, d)) : {_ == Nat.add(Nat.add(a, c), Nat.add(b, d)) : Nat}
  %ac.add_assoc_r(a, c, Nat.add(b, d)) : {Nat.add(a, Nat.add(b, Nat.add(c, d))) == _ : Nat}
  %ac.add_swap(c, b, d) : {Nat.add(a, _) == Nat.add(a, Nat.add(c, Nat.add(b, d))) : Nat}
  {==}

# (a + b) + c = (a + c) + b
def ac.add_rcomm(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(Nat.add(a, c), b) : Nat}:
  %ac.add_assoc_r(a, b, c) : {_ == Nat.add(Nat.add(a, c), b) : Nat}
  %ac.add_assoc_r(a, c, b) : {Nat.add(a, Nat.add(b, c)) == _ : Nat}
  %ac.add_comm(c, b) : {Nat.add(a, _) == Nat.add(a, Nat.add(c, b)) : Nat}
  {==}

def ac.add_cong_l(-a: Nat, -b: Nat, -c: Nat, e: {a == b : Nat}) -> {Nat.add(a, c) == Nat.add(b, c) : Nat}:
  %e : {Nat.add(a, c) == Nat.add(_, c) : Nat}
  {==}

def ac.add_cong_r(-c: Nat, -a: Nat, -b: Nat, e: {a == b : Nat}) -> {Nat.add(c, a) == Nat.add(c, b) : Nat}:
  %e : {Nat.add(c, a) == Nat.add(c, _) : Nat}
  {==}

def ac.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n++p:
      p
def ac.succ_inj(-a: Nat, -b: Nat, e: {1n+a == 1n+b : Nat}) -> {a == b : Nat}:
  %e : {a == ac.pred(_) : Nat}
  {==}


# nothing is below 0
def ac.lt0(-A: Type, b: Nat, h: {Nat.is_lt(b, 0n) == True{} : Bool}) -> A:
  match b:
    case 0n:
      ac.ft(A, h)
    case 1n++p:
      ac.ft(A, h)

# k + a = k + b gives a = b
def ac.add_inj(k: Nat, -a: Nat, -b: Nat, e: {Nat.add(k, a) == Nat.add(k, b) : Nat}) -> {a == b : Nat}:
  match k:
    case 0n:
      e
    case 1n++p:
      ac.add_inj(p, a, b, ac.succ_inj(Nat.add(p, a), Nat.add(p, b), e))

# Products
# --------

def ac.mul_zero(a: Nat) -> {Nat.mul(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      ac.mul_zero(p)

# (a + b) c = a c + b c
def ac.mul_add(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(Nat.add(p, b), c), Nat.add(Nat.mul(p, c), Nat.mul(b, c)), ac.mul_add(p, b, c)) : {Nat.add(c, _) == Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) : Nat}
      ac.add_assoc_r(c, Nat.mul(p, c), Nat.mul(b, c))

# a (1 + b) = a + a b
def ac.mul_succ_r(a: Nat, +b: Nat) -> {Nat.mul(a, 1n+b) == Nat.add(a, Nat.mul(a, b)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(p, 1n+b), Nat.add(p, Nat.mul(p, b)), ac.mul_succ_r(p, b)) : {1n+Nat.add(b, _) == 1n+Nat.add(p, Nat.add(b, Nat.mul(p, b))) : Nat}
      %ac.add_swap(b, p, Nat.mul(p, b)) : {1n+Nat.add(b, Nat.add(p, Nat.mul(p, b))) == 1n+_ : Nat}
      {==}

def ac.mul_comm(a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, ac.mul_zero(b))
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), ac.mul_succ_r(b, p)) : {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      %ac.mul_comm(p, b) : {Nat.add(b, Nat.mul(p, b)) == Nat.add(b, _) : Nat}
      {==}

def ac.mul_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(Nat.add(b, Nat.mul(p, b)), c), Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)), ac.mul_add(b, Nat.mul(p, b), c)) : {_ == Nat.add(Nat.mul(b, c), Nat.mul(p, Nat.mul(b, c))) : Nat}
      %ac.mul_assoc(p, b, c) : {Nat.add(Nat.mul(b, c), Nat.mul(Nat.mul(p, b), c)) == Nat.add(Nat.mul(b, c), _) : Nat}
      {==}

# (a b) c = (a c) b
def ac.mul_rcomm(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(Nat.mul(a, c), b) : Nat}:
  %Equal.sym(Nat, Nat.mul(Nat.mul(a, b), c), Nat.mul(a, Nat.mul(b, c)), ac.mul_assoc(a, b, c)) : {_ == Nat.mul(Nat.mul(a, c), b) : Nat}
  %Equal.sym(Nat, Nat.mul(Nat.mul(a, c), b), Nat.mul(a, Nat.mul(c, b)), ac.mul_assoc(a, c, b)) : {Nat.mul(a, Nat.mul(b, c)) == _ : Nat}
  %ac.mul_comm(b, c) : {Nat.mul(a, Nat.mul(b, c)) == Nat.mul(a, _) : Nat}
  {==}

# Order
# -----

def ac.cmp_cancel(k: Nat, +a: Nat, +b: Nat) -> {Nat.cmp(Nat.add(k, a), Nat.add(k, b)) == Nat.cmp(a, b) : Cmp}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      ac.cmp_cancel(p, a, b)

def ac.sub_cancel(k: Nat, +a: Nat, +b: Nat) -> {Nat.sub(Nat.add(k, a), Nat.add(k, b)) == Nat.sub(a, b) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      ac.sub_cancel(p, a, b)

def ac.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      {==}

def ac.sub_self(a: Nat) -> {Nat.sub(a, a) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      ac.sub_self(p)

# (a + b) - a = b
def ac.sub_add_l(a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      ac.sub_zero(b)
    case 1n++p:
      ac.sub_add_l(p, b)

# a - b = 0 for a <= b
def ac.sub_le(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n b:
      {==}
    case 1n++p 0n:
      ac.ft({Nat.sub(1n+p, 0n) == 0n : Nat}, h)
    case 1n++p 1n++q:
      ac.sub_le(p, q, h)

# a + (b - a) = b for a <= b
def ac.add_sub(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.add(a, Nat.sub(b, a)) == b : Nat}:
  match a b:
    case 0n b:
      ac.sub_zero(b)
    case 1n++p 0n:
      ac.ft({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, h)
    case 1n++p 1n++q:
      %ac.add_sub(p, q, h) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

# p + q = r gives r - q = p
def ac.sub_of_sum(+p: Nat, +q: Nat, -r: Nat, e: {Nat.add(p, q) == r : Nat}) -> {Nat.sub(r, q) == p : Nat}:
  %e : {Nat.sub(_, q) == p : Nat}
  %ac.add_comm(q, p) : {Nat.sub(_, q) == p : Nat}
  ac.sub_add_l(q, p)

def ac.cmp_refl(a: Nat) -> {Nat.cmp(a, a) == EQ{} : Cmp}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      ac.cmp_refl(p)

def ac.le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      ac.le_refl(p)

def ac.le_zero(a: Nat) -> {Nat.is_le(0n, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      {==}

def ac.le_add(a: Nat, +b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      ac.le_zero(b)
    case 1n++p:
      ac.le_add(p, b)

def ac.le_add_l(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  %ac.add_comm(b, a) : {Nat.is_le(b, _) == True{} : Bool}
  ac.le_add(b, a)

def ac.le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      ac.le_zero(c)
    case 1n++p 0n c:
      ac.ft({Nat.is_le(1n+p, c) == True{} : Bool}, h1)
    case 1n++p 1n++q 0n:
      ac.ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, h2)
    case 1n++p 1n++q 1n++r:
      ac.le_trans(p, q, r, h1, h2)

def ac.lt_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n b:
      ac.le_zero(b)
    case 1n++p 0n:
      ac.ft({Nat.is_le(1n+p, 0n) == True{} : Bool}, h)
    case 1n++p 1n++q:
      ac.lt_le(p, q, h)

# a < b <= c
def ac.lt_le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n c:
      ac.ft({Nat.is_lt(0n, c) == True{} : Bool}, h1)
    case 0n 1n++q 0n:
      ac.ft({Nat.is_lt(0n, 0n) == True{} : Bool}, h2)
    case 0n 1n++q 1n++r:
      {==}
    case 1n++p 0n c:
      ac.ft({Nat.is_lt(1n+p, c) == True{} : Bool}, h1)
    case 1n++p 1n++q 0n:
      ac.ft({Nat.is_lt(1n+p, 0n) == True{} : Bool}, h2)
    case 1n++p 1n++q 1n++r:
      ac.lt_le_trans(p, q, r, h1, h2)

# a <= b < c
def ac.le_lt_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case a b 0n:
      ac.lt0({Nat.is_lt(a, 0n) == True{} : Bool}, b, h2)
    case 0n b 1n++r:
      {==}
    case 1n++p 0n 1n++r:
      ac.ft({Nat.is_lt(1n+p, 1n+r) == True{} : Bool}, h1)
    case 1n++p 1n++q 1n++r:
      ac.le_lt_trans(p, q, r, h1, h2)

def ac.lt_zero_f(a: Nat) -> {Nat.is_lt(a, 0n) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      {==}

# the order as a Cmp
def ac.cmp_lt(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.cmp(a, b) == LT{} : Cmp}:
  match a b:
    case 0n 0n:
      ac.ft({EQ{} == LT{} : Cmp}, h)
    case 0n 1n++q:
      {==}
    case 1n++p 0n:
      ac.ft({GT{} == LT{} : Cmp}, h)
    case 1n++p 1n++q:
      ac.cmp_lt(p, q, h)

def ac.cmp_gt(a: Nat, b: Nat, h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.cmp(a, b) == GT{} : Cmp}:
  match a b:
    case 0n 0n:
      ac.ft({EQ{} == GT{} : Cmp}, h)
    case 0n 1n++q:
      ac.ft({LT{} == GT{} : Cmp}, h)
    case 1n++p 0n:
      {==}
    case 1n++p 1n++q:
      ac.cmp_gt(p, q, h)

# not a < b gives b <= a
def ac.le_of_not_lt(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool}) -> {Nat.is_le(b, a) == True{} : Bool}:
  match a b:
    case a 0n:
      ac.le_zero(a)
    case 0n 1n++q:
      ac.tf({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n++p 1n++q:
      ac.le_of_not_lt(p, q, h)

# a <= b and b < a are not both
def ac.le_not_lt(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n b:
      ac.lt_zero_f(b)
    case 1n++p 0n:
      ac.ft({Nat.is_lt(0n, 1n+p) == False{} : Bool}, h)
    case 1n++p 1n++q:
      ac.le_not_lt(p, q, h)

# a <= b <= a
def ac.le_antisym(a: Nat, b: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, a) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n++q:
      ac.ft({0n == 1n+q : Nat}, h2)
    case 1n++p 0n:
      ac.ft({1n+p == 0n : Nat}, h1)
    case 1n++p 1n++q:
      %ac.le_antisym(p, q, h1, h2) : {1n+p == 1n+_ : Nat}
      {==}

# k + a <= k + b is a <= b
def ac.le_cancel(k: Nat, +a: Nat, +b: Nat) -> {Nat.is_le(Nat.add(k, a), Nat.add(k, b)) == Nat.is_le(a, b) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      ac.le_cancel(p, a, b)

def ac.lt_cancel(k: Nat, +a: Nat, +b: Nat) -> {Nat.is_lt(Nat.add(k, a), Nat.add(k, b)) == Nat.is_lt(a, b) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n++p:
      ac.lt_cancel(p, a, b)

# 1 + b + x is not at most b
def ac.not_le_succ(b: Nat, +x: Nat) -> {Nat.is_le(Nat.add(1n+b, x), b) == False{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n++p:
      ac.not_le_succ(p, x)

def ac.lt_succ(a: Nat) -> {Nat.is_lt(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      ac.lt_succ(p)
def ac.le_add_mono(a: Nat, b: Nat, +c: Nat, +d: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  match a b:
    case 0n 0n:
      h2
    case 0n 1n++q:
      ac.le_trans(c, d, 1n+Nat.add(q, d), h2, ac.le_trans(d, Nat.add(q, d), 1n+Nat.add(q, d), ac.le_add_l(q, d), ac.lt_le(Nat.add(q, d), 1n+Nat.add(q, d), ac.lt_succ(Nat.add(q, d)))))
    case 1n++p 0n:
      ac.ft({Nat.is_le(1n+Nat.add(p, c), Nat.add(0n, d)) == True{} : Bool}, h1)
    case 1n++p 1n++q:
      ac.le_add_mono(p, q, c, d, h1, h2)


# a <= b is a < 1 + b
def ac.le_lt_succ(a: Nat, b: Nat) -> {Nat.is_le(a, b) == Nat.is_lt(a, 1n+b) : Bool}:
  match a b:
    case 0n b:
      ac.le_zero(b)
    case 1n++p 0n:
      Equal.sym(Bool, Nat.is_lt(p, 0n), False{}, ac.lt_zero_f(p))
    case 1n++p 1n++q:
      ac.le_lt_succ(p, q)

# a < b is 1 + a <= b
def ac.lt_le_succ(a: Nat, b: Nat) -> {Nat.is_lt(a, b) == Nat.is_le(1n+a, b) : Bool}:
  match a b:
    case a 0n:
      Equal.trans(Bool, Nat.is_lt(a, 0n), False{}, Nat.is_le(1n+a, 0n), ac.lt_zero_f(a), {==})
    case 0n 1n++q:
      Equal.sym(Bool, Nat.is_le(0n, q), True{}, ac.le_zero(q))
    case 1n++p 1n++q:
      ac.lt_le_succ(p, q)

# x <= 0 is x = 0
def ac.le0_eq(x: Nat, h: {Nat.is_le(x, 0n) == True{} : Bool}) -> {x == 0n : Nat}:
  match x:
    case 0n:
      {==}
    case 1n++p:
      ac.ft({1n+p == 0n : Nat}, h)

def ac.sub_le_self(a: Nat, b: Nat) -> {Nat.is_le(Nat.sub(a, b), a) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n++p 0n:
      ac.le_refl(p)
    case 1n++p 1n++q:
      ac.le_trans(Nat.sub(p, q), p, 1n+p, ac.sub_le_self(p, q), ac.lt_le(p, 1n+p, ac.lt_succ(p)))

# Bools
# -----

def ac.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def ac.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      ac.ft({b == True{} : Bool}, h)

def ac.and_i(-a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ha) : {Bool.and(_, b) == True{} : Bool}
  hb

# Division by 1 + bp
# ------------------

# a step of Nat.divmod.go keeps q (1 + bp) + r + (what is left) fixed,
# with m + r = bp
def ac.dm_go_eq(a: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat, +h: {Nat.add(m, r) == bp : Nat}) -> {Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(a, m, d, r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(a, m, d, r))) == Nat.add(a, Nat.add(Nat.mul(d, 1n+bp), r)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++ap:
      match m:
        case 0n:
          +lhs = Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(ap, r, 1n+d, 0n)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(ap, r, 1n+d, 0n)))
          +dm = Nat.mul(d, 1n+bp)
          +h2 = {%Equal.sym(Nat, Nat.add(r, 0n), r, ac.add_zero(r)) : {_ == bp : Nat}; h : {Nat.add(r, 0n) == bp : Nat}}
          +ih = ac.dm_go_eq(ap, r, 1n+d, 0n, bp, h2)
          +y = Nat.add(bp, dm)
          %Equal.sym(Nat, r, bp, h) : {lhs == 1n+Nat.add(ap, Nat.add(dm, _)) : Nat}
          %ac.add_comm(bp, dm) : {lhs == 1n+Nat.add(ap, _) : Nat}
          %ac.add_succ(ap, y) : {lhs == _ : Nat}
          %ac.add_zero(y) : {lhs == Nat.add(ap, 1n+_) : Nat}
          ih
        case 1n++mp:
          +lhs = Nat.add(Nat.mul(Pair.fst(Nat, Nat, Nat.divmod.go(ap, mp, d, 1n+r)), 1n+bp), Pair.snd(Nat, Nat, Nat.divmod.go(ap, mp, d, 1n+r)))
          +dm = Nat.mul(d, 1n+bp)
          +h3 = Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, ac.add_succ(mp, r), h)
          +ih = ac.dm_go_eq(ap, mp, d, 1n+r, bp, h3)
          %ac.add_succ(ap, Nat.add(dm, r)) : {lhs == _ : Nat}
          %ac.add_succ(dm, r) : {lhs == Nat.add(ap, _) : Nat}
          ih

def ac.dm_go_le(a: Nat, +m: Nat, +d: Nat, +r: Nat, +bp: Nat, +h: {Nat.add(m, r) == bp : Nat}) -> {Nat.is_le(Pair.snd(Nat, Nat, Nat.divmod.go(a, m, d, r)), bp) == True{} : Bool}:
  match a:
    case 0n:
      %h : {Nat.is_le(r, _) == True{} : Bool}
      ac.le_add_l(m, r)
    case 1n++ap:
      match m:
        case 0n:
          ac.dm_go_le(ap, r, 1n+d, 0n, bp, {%Equal.sym(Nat, Nat.add(r, 0n), r, ac.add_zero(r)) : {_ == bp : Nat}; h : {Nat.add(r, 0n) == bp : Nat}})
        case 1n++mp:
          ac.dm_go_le(ap, mp, d, 1n+r, bp, Equal.trans(Nat, Nat.add(mp, 1n+r), 1n+Nat.add(mp, r), bp, ac.add_succ(mp, r), h))

# x = (x / n) n + x mod n, for n = 1 + bp
def ac.div_eq(+x: Nat, +bp: Nat) -> {Nat.add(Nat.mul(Nat.div(x, 1n+bp), 1n+bp), Nat.mod(x, 1n+bp)) == x : Nat}:
  %ac.add_zero(x) : {Nat.add(Nat.mul(Nat.div(x, 1n+bp), 1n+bp), Nat.mod(x, 1n+bp)) == _ : Nat}
  ac.dm_go_eq(x, bp, 0n, 0n, bp, ac.add_zero(bp))

# x mod n < n, for n = 1 + bp
def ac.mod_le(+x: Nat, +bp: Nat) -> {Nat.is_le(Nat.mod(x, 1n+bp), bp) == True{} : Bool}:
  ac.dm_go_le(x, bp, 0n, 0n, bp, ac.add_zero(bp))

# q (1 + b) + r with r <= b fixes q
def ac.qr_unique(q1: Nat, q2: Nat, +r1: Nat, +r2: Nat, +b: Nat, e: {Nat.add(Nat.mul(q1, 1n+b), r1) == Nat.add(Nat.mul(q2, 1n+b), r2) : Nat}, h1: {Nat.is_le(r1, b) == True{} : Bool}, h2: {Nat.is_le(r2, b) == True{} : Bool}) -> {q1 == q2 : Nat}:
  match q1 q2:
    case 0n 0n:
      {==}
    case 0n 1n++p2:
      +e2 = {%ac.add_assoc(1n+b, Nat.mul(p2, 1n+b), r2) : {r1 == _ : Nat}; e : {r1 == Nat.add(1n+b, Nat.add(Nat.mul(p2, 1n+b), r2)) : Nat}}
      +h3 = {%e2 : {Nat.is_le(_, b) == True{} : Bool}; h1 : {Nat.is_le(Nat.add(1n+b, Nat.add(Nat.mul(p2, 1n+b), r2)), b) == True{} : Bool}}
      ac.ft({0n == 1n+p2 : Nat}, {%ac.not_le_succ(b, Nat.add(Nat.mul(p2, 1n+b), r2)) : {_ == True{} : Bool}; h3 : {False{} == True{} : Bool}})
    case 1n++p1 0n:
      +e2 = {%ac.add_assoc(1n+b, Nat.mul(p1, 1n+b), r1) : {_ == r2 : Nat}; e : {Nat.add(1n+b, Nat.add(Nat.mul(p1, 1n+b), r1)) == r2 : Nat}}
      +h3 = {%Equal.sym(Nat, Nat.add(1n+b, Nat.add(Nat.mul(p1, 1n+b), r1)), r2, e2) : {Nat.is_le(_, b) == True{} : Bool}; h2 : {Nat.is_le(Nat.add(1n+b, Nat.add(Nat.mul(p1, 1n+b), r1)), b) == True{} : Bool}}
      ac.ft({1n+p1 == 0n : Nat}, {%ac.not_le_succ(b, Nat.add(Nat.mul(p1, 1n+b), r1)) : {_ == True{} : Bool}; h3 : {False{} == True{} : Bool}})
    case 1n++p1 1n++p2:
      +e2 = {%ac.add_assoc(1n+b, Nat.mul(p1, 1n+b), r1) : {_ == Nat.add(1n+b, Nat.add(Nat.mul(p2, 1n+b), r2)) : Nat}; %ac.add_assoc(1n+b, Nat.mul(p2, 1n+b), r2) : {Nat.add(Nat.add(1n+b, Nat.mul(p1, 1n+b)), r1) == _ : Nat}; e : {Nat.add(1n+b, Nat.add(Nat.mul(p1, 1n+b), r1)) == Nat.add(1n+b, Nat.add(Nat.mul(p2, 1n+b), r2)) : Nat}}
      +e3 = ac.add_inj(1n+b, Nat.add(Nat.mul(p1, 1n+b), r1), Nat.add(Nat.mul(p2, 1n+b), r2), e2)
      %ac.qr_unique(p1, p2, r1, r2, b, e3, h1, h2) : {1n+p1 == 1n+_ : Nat}
      {==}

# n = q (1 + b) + r with r <= b: n / (1 + b) = q
def ac.div_unique(+n: Nat, +b: Nat, +q: Nat, +r: Nat, e: {Nat.add(Nat.mul(q, 1n+b), r) == n : Nat}, h: {Nat.is_le(r, b) == True{} : Bool}) -> {Nat.div(n, 1n+b) == q : Nat}:
  +e2 = Equal.trans(Nat, Nat.add(Nat.mul(Nat.div(n, 1n+b), 1n+b), Nat.mod(n, 1n+b)), n, Nat.add(Nat.mul(q, 1n+b), r), ac.div_eq(n, b), Equal.sym(Nat, Nat.add(Nat.mul(q, 1n+b), r), n, e))
  ac.qr_unique(Nat.div(n, 1n+b), q, Nat.mod(n, 1n+b), r, b, e2, ac.mod_le(n, b), h)

def ac.mul10_mono(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, 10n), Nat.mul(b, 10n)) == True{} : Bool}:
  match a b:
    case 0n b:
      ac.le_zero(Nat.mul(b, 10n))
    case 1n++p 0n:
      ac.ft({Nat.is_le(Nat.mul(1n+p, 10n), 0n) == True{} : Bool}, h)
    case 1n++p 1n++q:
      ac.mul10_mono(p, q, h)

# min
def ac.min_le(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.min(a, b) == a : Nat}:
  match a b:
    case 0n b:
      {==}
    case 1n++p 0n:
      ac.ft({Nat.min(1n+p, 0n) == 1n+p : Nat}, h)
    case 1n++p 1n++q:
      %ac.min_le(p, q, h) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

def ac.min_gt(a: Nat, b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.min(a, b) == b : Nat}:
  match a b:
    case 0n b:
      ac.tf({Nat.min(0n, b) == b : Nat}, Equal.trans(Bool, True{}, Nat.is_le(0n, b), False{}, Equal.sym(Bool, Nat.is_le(0n, b), True{}, ac.le_zero(b)), h))
    case 1n++p 0n:
      {==}
    case 1n++p 1n++q:
      %ac.min_gt(p, q, h) : {1n+Nat.min(p, q) == 1n+_ : Nat}
      {==}

# a < b: not b <= a
def ac.lt_not_le(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case a 0n:
      ac.lt0({Nat.is_le(0n, a) == False{} : Bool}, a, h)
    case 0n 1n++q:
      {==}
    case 1n++p 1n++q:
      ac.lt_not_le(p, q, h)
