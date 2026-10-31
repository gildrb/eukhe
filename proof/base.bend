# eukhe.com's Neovim: lemmas the proofs share
# ===========================================
#
# Facts about Bool, Nat, String and lists, used by every proof. The
# editor's own facts are in proof/base/: final.bend (what a settled editor
# holds), reach.bend (every editor the events reach is settled), text.bend
# (cells of the strings the screen shows).

import Base

# Logic
# -----

# G when b is True, Unit when False
def Bool.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True: anything follows
def Bool.false_true(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : Bool.If(_, G)
  Unit{}

# True is not False: anything follows
def Bool.true_false(-G: Type, e: {True{} == False{} : Bool}) -> G:
  Bool.false_true(G, Equal.sym(Bool, True{}, False{}, e))

# a Bool that is True is not False
def Bool.both(-G: Type, -b: Bool, t: {b == True{} : Bool}, f: {b == False{} : Bool}) -> G:
  Bool.false_true(G, Equal.trans(Bool, False{}, b, True{}, Equal.sym(Bool, b, False{}, f), t))

def And.l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Bool.false_true({False{} == True{} : Bool}, e)

def And.r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      Bool.false_true({b == True{} : Bool}, e)

def And.intro(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      Bool.false_true({False{} == True{} : Bool}, ha)

def Or.l(a: Bool, -b: Bool, ha: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      Bool.false_true({Bool.or(False{}, b) == True{} : Bool}, ha)

def Or.r(a: Bool, -b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

def Not.of(b: Bool, e: {b == False{} : Bool}) -> {Bool.not(b) == True{} : Bool}:
  match b:
    case True{}:
      Bool.true_false({False{} == True{} : Bool}, e)
    case False{}:
      {==}

# a pick between two values that both are x is x
def Pick.same(-A: Type, c: Bool, -x: A, -a: A, -b: A, ea: {a == x : A}, eb: {b == x : A}) -> {Bool.pick(A, c, a, b) == x : A}:
  match c:
    case True{}:
      ea
    case False{}:
      eb

# Nat
# ---

def LE(a: Nat, b: Nat) -> Data:
  {Nat.is_le(a, b) == True{} : Bool}

def LT(a: Nat, b: Nat) -> Data:
  {Nat.is_lt(a, b) == True{} : Bool}

def Nat.add_zero(a: Nat) -> {a == Nat.add(a, 0n) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_zero(p) : {1n+p == 1n+_ : Nat}
      {==}

def Nat.zero_r(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  Equal.sym(Nat, a, Nat.add(a, 0n), Nat.add_zero(a))

def Nat.add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def Nat.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      %Nat.add_zero(b) : {b == _ : Nat}
      {==}
    case 1n+p:
      %Nat.add_succ(b, p) : {1n+Nat.add(p, b) == _ : Nat}
      %Nat.add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

def Nat.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Nat.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def Nat.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Nat.le_refl(a: Nat) -> LE(a, a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.le_refl(p)

def Nat.le_zero(a: Nat) -> LE(0n, a):
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def Nat.le_succ(a: Nat, b: Nat, h: LE(a, b)) -> LE(a, 1n+b):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      Bool.false_true(LE(1n+p, 1n), h)
    case 1n+p 1n+q:
      Nat.le_succ(p, q, h)

def Nat.le_trans(a: Nat, b: Nat, c: Nat, h1: LE(a, b), h2: LE(b, c)) -> LE(a, c):
  match a b c:
    case 0n _ _:
      Nat.le_zero(c)
    case 1n+p 0n _:
      Bool.false_true(LE(1n+p, c), h1)
    case 1n+p 1n+q 0n:
      Bool.false_true(LE(1n+p, 0n), h2)
    case 1n+p 1n+q 1n+r:
      Nat.le_trans(p, q, r, h1, h2)

# a < b is 1 + a <= b
def Nat.lt_le(a: Nat, b: Nat, h: LT(a, b)) -> LE(1n+a, b):
  match a b:
    case 0n 0n:
      Bool.false_true(LE(1n, 0n), h)
    case 1n+p 0n:
      Bool.false_true(LE(2n+p, 0n), h)
    case 0n 1n+q:
      Nat.le_zero(q)
    case 1n+p 1n+q:
      Nat.lt_le(p, q, h)

def Nat.le_lt(a: Nat, b: Nat, h: LE(1n+a, b)) -> LT(a, b):
  match a b:
    case _ 0n:
      Bool.false_true(LT(a, 0n), h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      Nat.le_lt(p, q, h)

def Nat.lt_to_le(a: Nat, b: Nat, h: LT(a, b)) -> LE(a, b):
  match a b:
    case 0n 0n:
      Bool.false_true(LE(0n, 0n), h)
    case 1n+p 0n:
      Bool.false_true(LE(1n+p, 0n), h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      Nat.lt_to_le(p, q, h)

def Nat.lt_succ(+a: Nat) -> LT(a, 1n+a):
  Nat.le_lt(a, 1n+a, Nat.le_refl(1n+a))

def Nat.le_lt_trans(+a: Nat, +b: Nat, +c: Nat, h1: LE(a, b), h2: LT(b, c)) -> LT(a, c):
  Nat.le_lt(a, c, Nat.le_trans(1n+a, 1n+b, c, h1, Nat.lt_le(b, c, h2)))

# LE along equal bounds
def LE.cast_r(-a: Nat, -b: Nat, -c: Nat, e: {b == c : Nat}, h: LE(a, b)) -> LE(a, c):
  %e : LE(a, _)
  h

def LE.cast_l(-a: Nat, -b: Nat, -c: Nat, e: {a == b : Nat}, h: LE(a, c)) -> LE(b, c):
  %e : LE(_, c)
  h

# not a < b: b <= a
def Nat.not_lt(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == False{} : Bool}) -> LE(b, a):
  match a b:
    case _ 0n:
      Nat.le_zero(a)
    case 0n 1n+q:
      Bool.true_false(LE(1n+q, 0n), h)
    case 1n+p 1n+q:
      Nat.not_lt(p, q, h)

# not a <= b: b < a
def Nat.not_le(a: Nat, b: Nat, h: {Nat.is_le(a, b) == False{} : Bool}) -> LT(b, a):
  match a b:
    case 0n 0n:
      Bool.true_false(LT(0n, 0n), h)
    case 0n 1n+q:
      Bool.true_false(LT(1n+q, 0n), h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Nat.not_le(p, q, h)

# not a > b: a <= b
def Nat.not_gt(a: Nat, b: Nat, h: {Nat.is_gt(a, b) == False{} : Bool}) -> LE(a, b):
  match a b:
    case 0n _:
      Nat.le_zero(b)
    case 1n+p 0n:
      Bool.true_false(LE(1n+p, 0n), h)
    case 1n+p 1n+q:
      Nat.not_gt(p, q, h)

# a > b: b < a
def Nat.gt_lt(a: Nat, b: Nat, h: {Nat.is_gt(a, b) == True{} : Bool}) -> LT(b, a):
  match a b:
    case 0n 0n:
      Bool.false_true(LT(0n, 0n), h)
    case 0n 1n+q:
      Bool.false_true(LT(1n+q, 0n), h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Nat.gt_lt(p, q, h)

def Nat.lt_irrefl(-G: Type, a: Nat, h: LT(a, a)) -> G:
  match a:
    case 0n:
      Bool.false_true(G, h)
    case 1n+p:
      Nat.lt_irrefl(G, p, h)

# a <= b and b < a: anything follows
def Nat.le_lt_absurd(-G: Type, +a: Nat, b: Nat, h1: LE(a, b), h2: LT(b, a)) -> G:
  Nat.lt_irrefl(G, a, Nat.le_lt_trans(a, b, a, h1, h2))

def Nat.eq_refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.eq_refl(p)

def Nat.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Bool.false_true({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      Bool.false_true({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      %Nat.eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

# a < b: a is not b
def Nat.lt_ne(a: Nat, b: Nat, h: LT(a, b)) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      Bool.false_true({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 1n+p 0n:
      Bool.false_true({Nat.is_eq(1n+p, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      Nat.lt_ne(p, q, h)

def Nat.le_add(a: Nat, b: Nat) -> LE(a, Nat.add(a, b)):
  match a:
    case 0n:
      Nat.le_zero(b)
    case 1n+p:
      Nat.le_add(p, b)

def Nat.le_add_l(a: Nat, +b: Nat) -> LE(b, Nat.add(a, b)):
  match a:
    case 0n:
      Nat.le_refl(b)
    case 1n++p:
      Nat.le_succ(b, Nat.add(p, b), Nat.le_add_l(p, b))

# c <= d gives a + c <= a + d
def Nat.le_add_mono(a: Nat, -c: Nat, -d: Nat, h: LE(c, d)) -> LE(Nat.add(a, c), Nat.add(a, d)):
  match a:
    case 0n:
      h
    case 1n+p:
      Nat.le_add_mono(p, c, d, h)

def Nat.sub_le(a: Nat, b: Nat) -> LE(Nat.sub(a, b), a):
  match a b:
    case 0n _:
      {==}
    case 1n++p 0n:
      Nat.le_refl(p)
    case 1n+p 1n++q:
      Nat.le_succ(Nat.sub(p, q), p, Nat.sub_le(p, q))

# (a - b) + b == a, when b <= a
def Nat.sub_add(a: Nat, +b: Nat, h: LE(b, a)) -> {Nat.add(Nat.sub(a, b), b) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Bool.false_true({Nat.add(Nat.sub(0n, 1n+q), 1n+q) == 0n : Nat}, h)
    case 1n++p 0n:
      %Nat.add_zero(1n+p) : {_ == 1n+p : Nat}
      {==}
    case 1n+p 1n+q:
      %Nat.add_succ(Nat.sub(p, q), q) : {_ == 1n+p : Nat}
      %Nat.sub_add(p, q, h) : {1n+Nat.add(Nat.sub(p, q), q) == 1n+_ : Nat}
      {==}

# b + (a - b) == a, when b <= a
def Nat.add_sub(+a: Nat, +b: Nat, h: LE(b, a)) -> {Nat.add(b, Nat.sub(a, b)) == a : Nat}:
  %Nat.add_comm(Nat.sub(a, b), b) : {_ == a : Nat}
  Nat.sub_add(a, b, h)

# (b + a) - b == a
def Nat.add_sub_l(b: Nat, a: Nat) -> {Nat.sub(Nat.add(b, a), b) == a : Nat}:
  match b:
    case 0n:
      Nat.sub_zero(a)
    case 1n+q:
      Nat.add_sub_l(q, a)

# a <= b gives a - c <= b - c
def Nat.sub_mono(a: Nat, b: Nat, c: Nat, h: LE(a, b)) -> LE(Nat.sub(a, c), Nat.sub(b, c)):
  match a b c:
    case 0n _ _:
      Nat.le_zero(Nat.sub(b, c))
    case 1n+p 0n _:
      Bool.false_true(LE(Nat.sub(1n+p, c), Nat.sub(0n, c)), h)
    case 1n+p 1n+q 0n:
      h
    case 1n+p 1n+q 1n+r:
      Nat.sub_mono(p, q, r, h)

# b <= c gives a - c <= a - b
def Nat.sub_anti(a: Nat, b: Nat, c: Nat, h: LE(b, c)) -> LE(Nat.sub(a, c), Nat.sub(a, b)):
  match a b c:
    case 0n _ _:
      {==}
    case 1n+p 0n _:
      Nat.sub_le(1n+p, c)
    case 1n+p 1n+q 0n:
      Bool.false_true(LE(Nat.sub(1n+p, 0n), Nat.sub(1n+p, 1n+q)), h)
    case 1n+p 1n+q 1n+r:
      Nat.sub_anti(p, q, r, h)

# x - y <= t gives x <= t + y
def Nat.sub_le_add(x: Nat, y: Nat, +t: Nat, h: LE(Nat.sub(x, y), t)) -> LE(x, Nat.add(t, y)):
  match x y:
    case 0n _:
      Nat.le_zero(Nat.add(t, y))
    case 1n+p 0n:
      %Nat.add_zero(t) : LE(1n+p, _)
      h
    case 1n+p 1n+q:
      %Nat.add_succ(t, q) : LE(1n+p, _)
      Nat.sub_le_add(p, q, t, h)

# x <= t + y gives x - y <= t
def Nat.le_add_sub(x: Nat, y: Nat, +t: Nat, h: LE(x, Nat.add(t, y))) -> LE(Nat.sub(x, y), t):
  match x y:
    case 0n _:
      Nat.le_zero(t)
    case 1n+p 0n:
      LE.cast_r(1n+p, Nat.add(t, 0n), t, Nat.zero_r(t), h)
    case 1n+p 1n+q:
      Nat.le_add_sub(p, q, t, LE.cast_r(1n+p, Nat.add(t, 1n+q), 1n+Nat.add(t, q), Equal.sym(Nat, 1n+Nat.add(t, q), Nat.add(t, 1n+q), Nat.add_succ(t, q)), h))

def Nat.min_le_l(a: Nat, b: Nat) -> LE(Nat.min(a, b), a):
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Nat.min_le_l(p, q)

def Nat.min_le_r(a: Nat, b: Nat) -> LE(Nat.min(a, b), b):
  match a b:
    case 0n _:
      Nat.le_zero(b)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Nat.min_le_r(p, q)

def Nat.le_min(c: Nat, a: Nat, b: Nat, ha: LE(c, a), hb: LE(c, b)) -> LE(c, Nat.min(a, b)):
  match c a b:
    case 0n _ _:
      Nat.le_zero(Nat.min(a, b))
    case 1n+r 0n _:
      Bool.false_true(LE(1n+r, Nat.min(0n, b)), ha)
    case 1n+r 1n+p 0n:
      Bool.false_true(LE(1n+r, 0n), hb)
    case 1n+r 1n+p 1n+q:
      Nat.le_min(r, p, q, ha, hb)

def Nat.le_max_l(a: Nat, b: Nat) -> LE(a, Nat.max(a, b)):
  match a b:
    case 0n _:
      Nat.le_zero(b)
    case 1n+p 0n:
      Nat.le_refl(p)
    case 1n+p 1n+q:
      Nat.le_max_l(p, q)

def Nat.le_max_r(a: Nat, b: Nat) -> LE(b, Nat.max(a, b)):
  match a b:
    case 0n _:
      Nat.le_refl(b)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Nat.le_max_r(p, q)

def Nat.max_le(a: Nat, b: Nat, c: Nat, ha: LE(a, c), hb: LE(b, c)) -> LE(Nat.max(a, b), c):
  match a b c:
    case 0n _ _:
      hb
    case 1n+p 0n _:
      ha
    case 1n+p 1n+q 0n:
      Bool.false_true(LE(1n+Nat.max(p, q), 0n), ha)
    case 1n+p 1n+q 1n+r:
      Nat.max_le(p, q, r, ha, hb)

# a <= b gives a + d <= b + d
def Nat.le_addr(a: Nat, b: Nat, +d: Nat, h: LE(a, b)) -> LE(Nat.add(a, d), Nat.add(b, d)):
  match a b:
    case 0n _:
      Nat.le_add_l(b, d)
    case 1n+p 0n:
      Bool.false_true(LE(Nat.add(1n+p, d), d), h)
    case 1n+p 1n+q:
      Nat.le_addr(p, q, d, h)

# a <= b and c <= d give a + c <= b + d
def Nat.le_add2(+a: Nat, +b: Nat, +c: Nat, +d: Nat, h1: LE(a, b), h2: LE(c, d)) -> LE(Nat.add(a, c), Nat.add(b, d)):
  Nat.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), Nat.le_addr(a, b, c, h1), Nat.le_add_mono(b, c, d, h2))

# (a + l) - (a + x) == l - x
def Nat.sub_cancel_l(a: Nat, -l: Nat, -x: Nat) -> {Nat.sub(Nat.add(a, l), Nat.add(a, x)) == Nat.sub(l, x) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.sub_cancel_l(p, l, x)

# (l + a) - (x + a) == l - x
def Nat.sub_cancel_r(+l: Nat, +x: Nat, +a: Nat) -> {Nat.sub(Nat.add(l, a), Nat.add(x, a)) == Nat.sub(l, x) : Nat}:
  %Nat.add_comm(a, l) : {Nat.sub(_, Nat.add(x, a)) == Nat.sub(l, x) : Nat}
  %Nat.add_comm(a, x) : {Nat.sub(Nat.add(a, l), _) == Nat.sub(l, x) : Nat}
  Nat.sub_cancel_l(a, l, x)

# x - y == x - min(x, y)
def Nat.sub_min(x: Nat, y: Nat) -> {Nat.sub(x, y) == Nat.sub(x, Nat.min(x, y)) : Nat}:
  match x y:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Nat.sub_min(p, q)

# (1 + p) - p == 1
def Nat.succ_sub(p: Nat) -> {Nat.sub(1n+p, p) == 1n : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      Nat.succ_sub(q)

# half of n, rounded down
def Half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+k:
          1n+Half(k)

def Half.go(n: Nat, +d: Nat) -> {Pair.fst(Nat, Nat, Nat.divmod.go(n, 1n, d, 0n)) == Nat.add(d, Half(n)) : Nat}:
  match n:
    case 0n:
      Nat.add_zero(d)
    case 1n+p:
      match p:
        case 0n:
          Nat.add_zero(d)
        case 1n+k:
          %Nat.add_succ(d, Half(k)) : {Pair.fst(Nat, Nat, Nat.divmod.go(k, 1n, 1n+d, 0n)) == _ : Nat}
          Half.go(k, 1n+d)

def Half.twice(n: Nat) -> LE(Nat.add(Half(n), Half(n)), n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n++k:
          %Nat.add_succ(Half(k), Half(k)) : LE(1n+_, 2n+k)
          Half.twice(k)

# twice n / 2 is at most n
def Nat.div2_twice(+n: Nat) -> LE(Nat.add(Nat.div(n, 2n), Nat.div(n, 2n)), n):
  %Equal.sym(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(n, 1n, 0n, 0n)), Half(n), Half.go(n, 0n)) : LE(Nat.add(_, _), n)
  Half.twice(n)

def Half.pair(n: Nat) -> LE(Nat.add(Half(n), Half(1n+n)), n):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n++k:
          %Nat.add_succ(Half(k), Half(1n+k)) : LE(1n+_, 2n+k)
          Half.pair(k)

# n / 2 + (n + 1) / 2 is at most n
def Nat.div2_pair(+n: Nat) -> LE(Nat.add(Nat.div(n, 2n), Nat.div(1n+n, 2n)), n):
  %Equal.sym(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(n, 1n, 0n, 0n)), Half(n), Half.go(n, 0n)) : LE(Nat.add(_, Nat.div(1n+n, 2n)), n)
  %Equal.sym(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(1n+n, 1n, 0n, 0n)), Half(1n+n), Half.go(1n+n, 0n)) : LE(Nat.add(Half(n), _), n)
  Half.pair(n)

def Half.mono(n: Nat) -> LE(Half(n), Half(1n+n)):
  match n:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+k:
          Half.mono(k)

# n / 2 is at most (n + 1) / 2
def Nat.div2_mono(+n: Nat) -> LE(Nat.div(n, 2n), Nat.div(1n+n, 2n)):
  %Equal.sym(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(n, 1n, 0n, 0n)), Half(n), Half.go(n, 0n)) : LE(_, Nat.div(1n+n, 2n))
  %Equal.sym(Nat, Pair.fst(Nat, Nat, Nat.divmod.go(1n+n, 1n, 0n, 0n)), Half(1n+n), Half.go(1n+n, 0n)) : LE(Half(n), _)
  Half.mono(n)

# x + z <= y gives x <= y - z
def Nat.le_sub_of_add(+x: Nat, z: Nat, y: Nat, h: LE(Nat.add(x, z), y)) -> LE(x, Nat.sub(y, z)):
  match z y:
    case 0n _:
      LE.cast_r(x, y, Nat.sub(y, 0n), Equal.sym(Nat, Nat.sub(y, 0n), y, Nat.sub_zero(y)), LE.cast_l(Nat.add(x, 0n), x, y, Nat.zero_r(x), h))
    case 1n+q 0n:
      Bool.false_true(LE(x, 0n), LE.cast_l(Nat.add(x, 1n+q), 1n+Nat.add(x, q), 0n, Equal.sym(Nat, 1n+Nat.add(x, q), Nat.add(x, 1n+q), Nat.add_succ(x, q)), h))
    case 1n+q 1n+r:
      Nat.le_sub_of_add(x, q, r, LE.cast_l(Nat.add(x, 1n+q), 1n+Nat.add(x, q), 1n+r, Equal.sym(Nat, 1n+Nat.add(x, q), Nat.add(x, 1n+q), Nat.add_succ(x, q)), h))

# a + x <= a + y gives x <= y
def Nat.le_add_cancel(a: Nat, -x: Nat, -y: Nat, h: LE(Nat.add(a, x), Nat.add(a, y))) -> LE(x, y):
  match a:
    case 0n:
      h
    case 1n+p:
      Nat.le_add_cancel(p, x, y, h)

def Nat.sub_self(a: Nat) -> {Nat.sub(a, a) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Nat.sub_self(p)

# (1 + a) - b == 1 + (a - b) when b <= a
def Nat.sub_succ_l(a: Nat, b: Nat, h: LE(b, a)) -> {Nat.sub(1n+a, b) == 1n+Nat.sub(a, b) : Nat}:
  match a b:
    case _ 0n:
      Equal.cong(Nat, Nat, x => 1n+x, a, Nat.sub(a, 0n), Equal.sym(Nat, Nat.sub(a, 0n), a, Nat.sub_zero(a)))
    case 0n 1n+q:
      Bool.false_true({Nat.sub(1n, 1n+q) == 1n+Nat.sub(0n, 1n+q) : Nat}, h)
    case 1n+p 1n+q:
      Nat.sub_succ_l(p, q, h)

# c - (c - k) is at most k
def Nat.sub_sub_le(c: Nat, k: Nat) -> LE(Nat.sub(c, Nat.sub(c, k)), k):
  match c k:
    case 0n _:
      Nat.le_zero(k)
    case 1n+p 0n:
      LE.cast_l(0n, Nat.sub(p, p), 0n, Equal.sym(Nat, Nat.sub(p, p), 0n, Nat.sub_self(p)), {==})
    case 1n++p 1n++q:
      LE.cast_l(1n+Nat.sub(p, Nat.sub(p, q)), Nat.sub(1n+p, Nat.sub(p, q)), 1n+q, Equal.sym(Nat, Nat.sub(1n+p, Nat.sub(p, q)), 1n+Nat.sub(p, Nat.sub(p, q)), Nat.sub_succ_l(p, Nat.sub(p, q), Nat.sub_le(p, q))), Nat.sub_sub_le(p, q))

# c - (c - k) is at least 1 when c and k are
def Nat.sub_sub_pos(c: Nat, k: Nat, hc: LE(1n, c), hk: LE(1n, k)) -> LE(1n, Nat.sub(c, Nat.sub(c, k))):
  match c k:
    case 0n _:
      Bool.false_true(LE(1n, Nat.sub(0n, Nat.sub(0n, k))), hc)
    case 1n+p 0n:
      Bool.false_true(LE(1n, Nat.sub(1n+p, Nat.sub(1n+p, 0n))), hk)
    case 1n++p 1n++q:
      LE.cast_r(1n, 1n+Nat.sub(p, Nat.sub(p, q)), Nat.sub(1n+p, Nat.sub(p, q)), Equal.sym(Nat, Nat.sub(1n+p, Nat.sub(p, q)), 1n+Nat.sub(p, Nat.sub(p, q)), Nat.sub_succ_l(p, Nat.sub(p, q), Nat.sub_le(p, q))), Nat.le_zero(Nat.sub(p, Nat.sub(p, q))))

def Nat.min_zero_r(a: Nat) -> {Nat.min(a, 0n) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# min(n, h) == h when h <= n
def Nat.min_eq_r(n: Nat, h: Nat, e: LE(h, n)) -> {Nat.min(n, h) == h : Nat}:
  match n h:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      Bool.false_true({Nat.min(0n, 1n+q) == 1n+q : Nat}, e)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.min(p, q), q, Nat.min_eq_r(p, q, e))

# 1 + (h - 1) == h when 1 <= h
def Nat.succ_pred(h: Nat, e: LE(1n, h)) -> {1n+Nat.sub(h, 1n) == h : Nat}:
  match h:
    case 0n:
      Bool.false_true({1n+Nat.sub(0n, 1n) == 0n : Nat}, e)
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.sub(p, 0n), p, Nat.sub_zero(p))

# (b - a) + (c - b) == c - a when a <= b <= c
def Nat.sub_chain(a: Nat, +b: Nat, +c: Nat, h1: LE(a, b), h2: LE(b, c)) -> {Nat.add(Nat.sub(b, a), Nat.sub(c, b)) == Nat.sub(c, a) : Nat}:
  match a b c:
    case 0n _ _:
      %Equal.sym(Nat, Nat.sub(b, 0n), b, Nat.sub_zero(b)) : {Nat.add(_, Nat.sub(c, b)) == Nat.sub(c, 0n) : Nat}
      %Equal.sym(Nat, Nat.sub(c, 0n), c, Nat.sub_zero(c)) : {Nat.add(b, Nat.sub(c, b)) == _ : Nat}
      Nat.add_sub(c, b, h2)
    case 1n+p 0n _:
      Bool.false_true({Nat.add(Nat.sub(0n, 1n+p), Nat.sub(c, 0n)) == Nat.sub(c, 1n+p) : Nat}, h1)
    case 1n+p 1n+q 0n:
      Bool.false_true({Nat.add(Nat.sub(1n+q, 1n+p), Nat.sub(0n, 1n+q)) == Nat.sub(0n, 1n+p) : Nat}, h2)
    case 1n+p 1n+q 1n+r:
      Nat.sub_chain(p, q, r, h1, h2)

# a < b gives 0 < b - a
def Nat.sub_pos(a: Nat, b: Nat, h: LT(a, b)) -> LT(0n, Nat.sub(b, a)):
  match a b:
    case 0n 0n:
      Bool.false_true(LT(0n, 0n), h)
    case 1n+p 0n:
      Bool.false_true(LT(0n, 0n), h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      Nat.sub_pos(p, q, h)

# b <= a: not a < b
def Nat.le_not_lt(a: Nat, b: Nat, h: LE(b, a)) -> {Nat.is_lt(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 1n+p 0n:
      {==}
    case 0n 1n+q:
      Bool.false_true({Nat.is_lt(0n, 1n+q) == False{} : Bool}, h)
    case 1n+p 1n+q:
      Nat.le_not_lt(p, q, h)
