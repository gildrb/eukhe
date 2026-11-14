# eukhe: lemmas for the reachable-tree laws of area agent_tree (prefix at_reach.)
#
# One invariant, at_reach.Good(t, k): local conditions between each split
# and its two children (the split tiles its scope, a node that does not
# run has children that do not run, the budget fits, the children's
# deadlines are at most the node's, and a split uses one level of the
# depth budget k). Good holds at init and after every event; Compat(n, m)
# says the subtree m may replace n under any Good parent. Every reachable
# law then reads off Good.

import Base
import ../../../bend/agent_tree.bend as T
import ../../../spec/agents/agent_tree.bend as S

# Logic
# -----

def at_reach.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def at_reach.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : at_reach.BD(_, A, Unit)
  Unit{}

def at_reach.absurd_t(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : at_reach.BD(_, Unit, A)
  Unit{}

def at_reach.tr(-A: Type, -x: A, -y: A, -F: A -> Type, e: {x == y : A}, h: F(x)) -> F(y):
  %e : F(_)
  h

def at_reach.And(A: Data, B: Data) -> Data:
  +Sigma<A, _ => B>

def at_reach.and_t(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  eb

def at_reach.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      at_reach.absurd({False{} == True{} : Bool}, h)

def at_reach.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      at_reach.absurd({b == True{} : Bool}, h)

def at_reach.or_r(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def at_reach.or_not_b(b: Bool) -> {Bool.or(Bool.not(b), b) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def at_reach.not_t(x: Bool, h: {Bool.not(x) == True{} : Bool}) -> {x == False{} : Bool}:
  match x:
    case True{}:
      at_reach.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def at_reach.not_f(x: Bool, h: {x == False{} : Bool}) -> {Bool.not(x) == True{} : Bool}:
  match x:
    case True{}:
      at_reach.absurd_t({False{} == True{} : Bool}, h)
    case False{}:
      {==}

# rn false and (rm implies rn): rm false
def at_reach.run_down(rn: Bool, rm: Bool, h: {Bool.or(Bool.not(rm), rn) == True{} : Bool}, e: {rn == False{} : Bool}) -> {rm == False{} : Bool}:
  match rn rm:
    case True{} True{}:
      at_reach.absurd_t({True{} == False{} : Bool}, e)
    case True{} False{}:
      {==}
    case False{} True{}:
      at_reach.absurd({True{} == False{} : Bool}, h)
    case False{} False{}:
      {==}

# Nat
# ---

def at_reach.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def at_reach.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      at_reach.le_refl(p)

def at_reach.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n y z:
      at_reach.le0(z)
    case 1n+x 0n z:
      at_reach.absurd({Nat.is_le(1n+x, z) == True{} : Bool}, ab)
    case 1n+x 1n+y 0n:
      at_reach.absurd({False{} == True{} : Bool}, bc)
    case 1n+x 1n+y 1n+z:
      at_reach.le_trans(x, y, z, ab, bc)

def at_reach.le_succ_r(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n y:
      {==}
    case 1n+x 0n:
      at_reach.absurd({Nat.is_le(1n+x, 1n+0n) == True{} : Bool}, h)
    case 1n+x 1n+y:
      at_reach.le_succ_r(x, y, h)

def at_reach.le_add_r(+a: Nat, +c: Nat) -> {Nat.is_le(a, Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      at_reach.le0(c)
    case 1n+p:
      at_reach.le_add_r(p, c)

def at_reach.sub_le(+x: Nat, +n: Nat) -> {Nat.is_le(Nat.sub(x, n), x) == True{} : Bool}:
  match x n:
    case 0n q:
      {==}
    case 1n+p 0n:
      at_reach.le_refl(1n+p)
    case 1n+p 1n+q:
      at_reach.le_succ_r(Nat.sub(p, q), p, at_reach.sub_le(p, q))

def at_reach.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %at_reach.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def at_reach.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %at_reach.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def at_reach.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %at_reach.add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def at_reach.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, at_reach.add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), at_reach.add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %at_reach.add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# a + (b + c) = b + (a + c)
def at_reach.add_lcomm(+a: Nat, +b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  %at_reach.add_assoc(a, b, c) : {_ == Nat.add(b, Nat.add(a, c)) : Nat}
  %Equal.sym(Nat, Nat.add(a, b), Nat.add(b, a), at_reach.add_comm(a, b)) : {Nat.add(_, c) == Nat.add(b, Nat.add(a, c)) : Nat}
  at_reach.add_assoc(b, a, c)

def at_reach.add_mono_l(c: Nat, -a: Nat, -b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(c, a), Nat.add(c, b)) == True{} : Bool}:
  match c:
    case 0n:
      h
    case 1n+p:
      at_reach.add_mono_l(p, a, b, h)

def at_reach.add_mono_r(+a: Nat, +b: Nat, +c: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, c)) == True{} : Bool}:
  %at_reach.add_comm(c, a) : {Nat.is_le(_, Nat.add(b, c)) == True{} : Bool}
  %at_reach.add_comm(c, b) : {Nat.is_le(Nat.add(c, a), _) == True{} : Bool}
  at_reach.add_mono_l(c, a, b, h)

def at_reach.max_le(a: Nat, b: Nat, k: Nat, ha: {Nat.is_le(a, k) == True{} : Bool}, hb: {Nat.is_le(b, k) == True{} : Bool}) -> {Nat.is_le(Nat.max(a, b), k) == True{} : Bool}:
  match a b k:
    case 0n y z:
      hb
    case 1n+x 0n z:
      ha
    case 1n+x 1n+y 0n:
      at_reach.absurd({False{} == True{} : Bool}, ha)
    case 1n+x 1n+y 1n+z:
      at_reach.max_le(x, y, z, ha, hb)

# y + x <= m when y <= m and x <= m - y
def at_reach.fit_sub(y: Nat, +x: Nat, m: Nat, h1: {Nat.is_le(y, m) == True{} : Bool}, h2: {Nat.is_le(x, Nat.sub(m, y)) == True{} : Bool}) -> {Nat.is_le(Nat.add(y, x), m) == True{} : Bool}:
  match y m:
    case 0n 0n:
      h2
    case 0n 1n+q:
      h2
    case 1n+p 0n:
      at_reach.absurd({Nat.is_le(Nat.add(1n+p, x), 0n) == True{} : Bool}, h1)
    case 1n+p 1n+q:
      at_reach.fit_sub(p, x, q, h1, h2)

def at_reach.sub_sub(m: Nat, x: Nat, -y: Nat) -> {Nat.sub(Nat.sub(m, x), y) == Nat.sub(m, Nat.add(x, y)) : Nat}:
  match m x:
    case 0n 0n:
      {==}
    case 0n 1n+p:
      {==}
    case 1n+q 0n:
      {==}
    case 1n+q 1n+p:
      at_reach.sub_sub(q, p, y)

# h + (c - h) = c when h <= c
def at_reach.sub_add(h: Nat, c: Nat, e: {Nat.is_le(h, c) == True{} : Bool}) -> {Nat.add(h, Nat.sub(c, h)) == c : Nat}:
  match h c:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      at_reach.absurd({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, e)
    case 1n+p 1n+q:
      %at_reach.sub_add(p, q, e) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

def at_reach.half_le(+c: Nat) -> {Nat.is_le(T.half(c), c) == True{} : Bool}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      match p:
        case 0n:
          {==}
        case 1n+q:
          at_reach.le_succ_r(T.half(q), q, at_reach.half_le(q))

def at_reach.halves_sum(+c: Nat) -> {Nat.add(Nat.sub(c, T.half(c)), T.half(c)) == c : Nat}:
  Equal.trans(Nat, Nat.add(Nat.sub(c, T.half(c)), T.half(c)), Nat.add(T.half(c), Nat.sub(c, T.half(c))), c, at_reach.add_comm(Nat.sub(c, T.half(c)), T.half(c)), at_reach.sub_add(T.half(c), c, at_reach.half_le(c)))

# a spend that fits the free budget keeps the sum within m
def at_reach.spend_arith(+m: Nat, +s: Nat, +a: Nat, +b: Nat, +n: Nat, inv: {Nat.is_le(Nat.add(s, Nat.add(a, b)), m) == True{} : Bool}, fit: {Nat.is_le(n, Nat.sub(Nat.sub(Nat.sub(m, s), a), b)) == True{} : Bool}) -> {Nat.is_le(Nat.add(Nat.add(s, n), Nat.add(a, b)), m) == True{} : Bool}:
  +eq = Equal.trans(Nat, Nat.sub(Nat.sub(Nat.sub(m, s), a), b), Nat.sub(Nat.sub(m, s), Nat.add(a, b)), Nat.sub(m, Nat.add(s, Nat.add(a, b))), at_reach.sub_sub(Nat.sub(m, s), a, b), at_reach.sub_sub(m, s, Nat.add(a, b)))
  +f = at_reach.fit_sub(Nat.add(s, Nat.add(a, b)), n, m, inv, at_reach.tr(Nat, Nat.sub(Nat.sub(Nat.sub(m, s), a), b), Nat.sub(m, Nat.add(s, Nat.add(a, b))), z => {Nat.is_le(n, z) == True{} : Bool}, eq, fit))
  %Equal.sym(Nat, Nat.add(Nat.add(s, n), Nat.add(a, b)), Nat.add(s, Nat.add(n, Nat.add(a, b))), at_reach.add_assoc(s, n, Nat.add(a, b))) : {Nat.is_le(_, m) == True{} : Bool}
  %at_reach.add_comm(Nat.add(a, b), n) : {Nat.is_le(Nat.add(s, _), m) == True{} : Bool}
  %at_reach.add_assoc(s, Nat.add(a, b), n) : {Nat.is_le(_, m) == True{} : Bool}
  f

# a redo of the left child within the free budget keeps the sum within m
def at_reach.redo_arith_l(+m: Nat, +s: Nat, +a: Nat, +b: Nat, +x: Nat, inv: {Nat.is_le(Nat.add(s, Nat.add(a, b)), m) == True{} : Bool}, fit: {Nat.is_le(x, Nat.sub(Nat.sub(Nat.sub(m, s), a), b)) == True{} : Bool}) -> {Nat.is_le(Nat.add(s, Nat.add(Nat.add(a, x), b)), m) == True{} : Bool}:
  +eq = Equal.trans(Nat, Nat.sub(Nat.sub(Nat.sub(m, s), a), b), Nat.sub(Nat.sub(m, s), Nat.add(a, b)), Nat.sub(m, Nat.add(s, Nat.add(a, b))), at_reach.sub_sub(Nat.sub(m, s), a, b), at_reach.sub_sub(m, s, Nat.add(a, b)))
  +f = at_reach.fit_sub(Nat.add(s, Nat.add(a, b)), x, m, inv, at_reach.tr(Nat, Nat.sub(Nat.sub(Nat.sub(m, s), a), b), Nat.sub(m, Nat.add(s, Nat.add(a, b))), z => {Nat.is_le(x, z) == True{} : Bool}, eq, fit))
  %Equal.sym(Nat, Nat.add(Nat.add(a, x), b), Nat.add(a, Nat.add(x, b)), at_reach.add_assoc(a, x, b)) : {Nat.is_le(Nat.add(s, _), m) == True{} : Bool}
  %at_reach.add_comm(b, x) : {Nat.is_le(Nat.add(s, Nat.add(a, _)), m) == True{} : Bool}
  %at_reach.add_assoc(a, b, x) : {Nat.is_le(Nat.add(s, _), m) == True{} : Bool}
  %at_reach.add_assoc(s, Nat.add(a, b), x) : {Nat.is_le(_, m) == True{} : Bool}
  f

# a redo of the right child within the free budget keeps the sum within m
def at_reach.redo_arith_r(+m: Nat, +s: Nat, +a: Nat, +b: Nat, +x: Nat, inv: {Nat.is_le(Nat.add(s, Nat.add(a, b)), m) == True{} : Bool}, fit: {Nat.is_le(x, Nat.sub(Nat.sub(Nat.sub(m, s), a), b)) == True{} : Bool}) -> {Nat.is_le(Nat.add(s, Nat.add(a, Nat.add(b, x))), m) == True{} : Bool}:
  +eq = Equal.trans(Nat, Nat.sub(Nat.sub(Nat.sub(m, s), a), b), Nat.sub(Nat.sub(m, s), Nat.add(a, b)), Nat.sub(m, Nat.add(s, Nat.add(a, b))), at_reach.sub_sub(Nat.sub(m, s), a, b), at_reach.sub_sub(m, s, Nat.add(a, b)))
  +f = at_reach.fit_sub(Nat.add(s, Nat.add(a, b)), x, m, inv, at_reach.tr(Nat, Nat.sub(Nat.sub(Nat.sub(m, s), a), b), Nat.sub(m, Nat.add(s, Nat.add(a, b))), z => {Nat.is_le(x, z) == True{} : Bool}, eq, fit))
  %at_reach.add_assoc(a, b, x) : {Nat.is_le(Nat.add(s, _), m) == True{} : Bool}
  %at_reach.add_assoc(s, Nat.add(a, b), x) : {Nat.is_le(_, m) == True{} : Bool}
  f

# sp + (a2 + b2) <= sp + (a + b) when a2 == a and b2 == b
def at_reach.le_kids(+sp: Nat, -a2: Nat, +a: Nat, -b2: Nat, +b: Nat, ea: {a2 == a : Nat}, eb: {b2 == b : Nat}) -> {Nat.is_le(Nat.add(sp, Nat.add(a2, b2)), Nat.add(sp, Nat.add(a, b))) == True{} : Bool}:
  %Equal.sym(Nat, a2, a, ea) : {Nat.is_le(Nat.add(sp, Nat.add(_, b2)), Nat.add(sp, Nat.add(a, b))) == True{} : Bool}
  %Equal.sym(Nat, b2, b, eb) : {Nat.is_le(Nat.add(sp, Nat.add(a, _)), Nat.add(sp, Nat.add(a, b))) == True{} : Bool}
  at_reach.le_refl(Nat.add(sp, Nat.add(a, b)))

def at_reach.size_kids(-a2: Nat, -a: Nat, -b2: Nat, -b: Nat, ea: {a2 == a : Nat}, eb: {b2 == b : Nat}) -> {1n+Nat.add(a2, b2) == 1n+Nat.add(a, b) : Nat}:
  %Equal.sym(Nat, a2, a, ea) : {1n+Nat.add(_, b2) == 1n+Nat.add(a, b) : Nat}
  %Equal.sym(Nat, b2, b, eb) : {1n+Nat.add(a, _) == 1n+Nat.add(a, b) : Nat}
  {==}

# 1 + (n + r) = e + (1 + (l + r)) when n = e + l
def at_reach.size_l(+e: Nat, +sl: Nat, -sn: Nat, +sr: Nat, h: {sn == Nat.add(e, sl) : Nat}) -> {1n+Nat.add(sn, sr) == Nat.add(e, 1n+Nat.add(sl, sr)) : Nat}:
  %Equal.sym(Nat, sn, Nat.add(e, sl), h) : {1n+Nat.add(_, sr) == Nat.add(e, 1n+Nat.add(sl, sr)) : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(e, sl), sr), Nat.add(e, Nat.add(sl, sr)), at_reach.add_assoc(e, sl, sr)) : {1n+_ == Nat.add(e, 1n+Nat.add(sl, sr)) : Nat}
  Equal.sym(Nat, Nat.add(e, 1n+Nat.add(sl, sr)), 1n+Nat.add(e, Nat.add(sl, sr)), at_reach.add_succ(e, Nat.add(sl, sr)))

# 1 + (l + n) = e + (1 + (l + r)) when n = e + r
def at_reach.size_r(+e: Nat, +sl: Nat, -sn: Nat, +sr: Nat, h: {sn == Nat.add(e, sr) : Nat}) -> {1n+Nat.add(sl, sn) == Nat.add(e, 1n+Nat.add(sl, sr)) : Nat}:
  %Equal.sym(Nat, sn, Nat.add(e, sr), h) : {1n+Nat.add(sl, _) == Nat.add(e, 1n+Nat.add(sl, sr)) : Nat}
  %Equal.sym(Nat, Nat.add(sl, Nat.add(e, sr)), Nat.add(e, Nat.add(sl, sr)), at_reach.add_lcomm(sl, e, sr)) : {1n+_ == Nat.add(e, 1n+Nat.add(sl, sr)) : Nat}
  Equal.sym(Nat, Nat.add(e, 1n+Nat.add(sl, sr)), 1n+Nat.add(e, Nat.add(sl, sr)), at_reach.add_succ(e, Nat.add(sl, sr)))

# Lim
# ---

# a + b, Unlimited absorbing
def at_reach.lplus(a: T.Lim, b: T.Lim) -> T.Lim:
  match a:
    case T.Unlimited{}:
      T.Unlimited{}
    case T.Value{x}:
      match b:
        case T.Unlimited{}:
          T.Unlimited{}
        case T.Value{y}:
          T.Value{Nat.add(x, y)}

def at_reach.le_unl(a: T.Lim) -> {S.lim_le(a, T.Unlimited{}) == True{} : Bool}:
  match a:
    case T.Unlimited{}:
      {==}
    case T.Value{x}:
      {==}

def at_reach.lim_le_refl(a: T.Lim) -> {S.lim_le(a, a) == True{} : Bool}:
  match a:
    case T.Unlimited{}:
      {==}
    case T.Value{x}:
      at_reach.le_refl(x)

def at_reach.lim_le_trans(a: T.Lim, b: T.Lim, c: T.Lim, ab: {S.lim_le(a, b) == True{} : Bool}, bc: {S.lim_le(b, c) == True{} : Bool}) -> {S.lim_le(a, c) == True{} : Bool}:
  match a b c:
    case T.Unlimited{} T.Unlimited{} T.Unlimited{}:
      {==}
    case T.Unlimited{} T.Unlimited{} T.Value{z}:
      at_reach.absurd({False{} == True{} : Bool}, bc)
    case T.Unlimited{} T.Value{y} T.Unlimited{}:
      {==}
    case T.Unlimited{} T.Value{y} T.Value{z}:
      at_reach.absurd({False{} == True{} : Bool}, ab)
    case T.Value{x} T.Unlimited{} T.Unlimited{}:
      {==}
    case T.Value{x} T.Unlimited{} T.Value{z}:
      at_reach.absurd({Nat.is_le(x, z) == True{} : Bool}, bc)
    case T.Value{x} T.Value{y} T.Unlimited{}:
      {==}
    case T.Value{x} T.Value{y} T.Value{z}:
      at_reach.le_trans(x, y, z, ab, bc)

def at_reach.lplus_mono_l(x: T.Lim, y: T.Lim, c: T.Lim, h: {S.lim_le(x, y) == True{} : Bool}) -> {S.lim_le(at_reach.lplus(x, c), at_reach.lplus(y, c)) == True{} : Bool}:
  match x y c:
    case T.Unlimited{} T.Unlimited{} T.Unlimited{}:
      {==}
    case T.Unlimited{} T.Unlimited{} T.Value{w}:
      {==}
    case T.Unlimited{} T.Value{b} T.Unlimited{}:
      {==}
    case T.Unlimited{} T.Value{b} T.Value{w}:
      at_reach.absurd({False{} == True{} : Bool}, h)
    case T.Value{a} T.Unlimited{} T.Unlimited{}:
      {==}
    case T.Value{a} T.Unlimited{} T.Value{w}:
      {==}
    case T.Value{a} T.Value{b} T.Unlimited{}:
      {==}
    case T.Value{a} T.Value{b} T.Value{w}:
      at_reach.add_mono_r(a, b, w, h)

def at_reach.lplus_mono_r(a: T.Lim, x: T.Lim, y: T.Lim, h: {S.lim_le(x, y) == True{} : Bool}) -> {S.lim_le(at_reach.lplus(a, x), at_reach.lplus(a, y)) == True{} : Bool}:
  match a x y:
    case T.Unlimited{} u v:
      {==}
    case T.Value{n} T.Unlimited{} T.Unlimited{}:
      {==}
    case T.Value{n} T.Unlimited{} T.Value{w}:
      at_reach.absurd({False{} == True{} : Bool}, h)
    case T.Value{n} T.Value{b} T.Unlimited{}:
      {==}
    case T.Value{n} T.Value{b} T.Value{w}:
      at_reach.add_mono_l(n, b, w, h)

def at_reach.has_le(-x: Nat, l: T.Lim, h: {S.has(x, l) == True{} : Bool}) -> {S.lim_le(T.Value{x}, l) == True{} : Bool}:
  match l:
    case T.Unlimited{}:
      {==}
    case T.Value{m}:
      h

def at_reach.le_has(-x: Nat, l: T.Lim, h: {S.lim_le(T.Value{x}, l) == True{} : Bool}) -> {S.has(x, l) == True{} : Bool}:
  match l:
    case T.Unlimited{}:
      {==}
    case T.Value{m}:
      h

def at_reach.has0(l: T.Lim) -> {S.has(0n, l) == True{} : Bool}:
  match l:
    case T.Unlimited{}:
      {==}
    case T.Value{m}:
      at_reach.le0(m)

def at_reach.dl_less(dl: T.Lim, +margin: Nat) -> {S.lim_le(T.lim_less(dl, margin), dl) == True{} : Bool}:
  match dl:
    case T.Unlimited{}:
      {==}
    case T.Value{x}:
      at_reach.sub_le(x, margin)

def at_reach.regrant_has(f: T.Lim, +sp: Nat, +x: Nat) -> {S.has(sp, T.regrant(f, sp, x)) == True{} : Bool}:
  match f:
    case T.Unlimited{}:
      {==}
    case T.Value{m}:
      at_reach.le_add_r(sp, x)

# the parent's own spend plus smaller holds stays within its limit
def at_reach.bu_mono(+sp: Nat, +lim: T.Lim, +hl2: T.Lim, +hl: T.Lim, +hr2: T.Lim, +hr: T.Lim, el: {S.lim_le(hl2, hl) == True{} : Bool}, er: {S.lim_le(hr2, hr) == True{} : Bool}, bu: {S.lim_le(at_reach.lplus(T.Value{sp}, at_reach.lplus(hl, hr)), lim) == True{} : Bool}) -> {S.lim_le(at_reach.lplus(T.Value{sp}, at_reach.lplus(hl2, hr2)), lim) == True{} : Bool}:
  at_reach.lim_le_trans(at_reach.lplus(T.Value{sp}, at_reach.lplus(hl2, hr2)), at_reach.lplus(T.Value{sp}, at_reach.lplus(hl, hr)), lim, at_reach.lplus_mono_r(T.Value{sp}, at_reach.lplus(hl2, hr2), at_reach.lplus(hl, hr), at_reach.lim_le_trans(at_reach.lplus(hl2, hr2), at_reach.lplus(hl, hr2), at_reach.lplus(hl, hr), at_reach.lplus_mono_l(hl2, hl, hr2, el), at_reach.lplus_mono_r(hl, hr2, hr, er))), bu)

# a leaf's spend that fits its free budget
def at_reach.lleaf(lim: T.Lim, sp: Nat, +n: Nat, inv: {S.has(sp, lim) == True{} : Bool}, fit: {T.lim_fits(n, T.lim_less(lim, sp)) == True{} : Bool}) -> {S.has(Nat.add(sp, n), lim) == True{} : Bool}:
  match lim:
    case T.Unlimited{}:
      {==}
    case T.Value{m}:
      at_reach.fit_sub(sp, n, m, inv, fit)

# a split's spend that fits its free budget
def at_reach.lspend(lim: T.Lim, +sp: Nat, +n: Nat, hl: T.Lim, hr: T.Lim, inv: {S.lim_le(at_reach.lplus(T.Value{sp}, at_reach.lplus(hl, hr)), lim) == True{} : Bool}, fit: {T.lim_fits(n, T.lim_drop(T.lim_drop(T.lim_less(lim, sp), hl), hr)) == True{} : Bool}) -> {S.lim_le(at_reach.lplus(T.Value{Nat.add(sp, n)}, at_reach.lplus(hl, hr)), lim) == True{} : Bool}:
  match lim hl hr:
    case T.Unlimited{} u v:
      at_reach.le_unl(at_reach.lplus(T.Value{Nat.add(sp, n)}, at_reach.lplus(u, v)))
    case T.Value{m} T.Unlimited{} v:
      at_reach.absurd({S.lim_le(at_reach.lplus(T.Value{Nat.add(sp, n)}, at_reach.lplus(T.Unlimited{}, v)), T.Value{m}) == True{} : Bool}, inv)
    case T.Value{m} T.Value{a} T.Unlimited{}:
      at_reach.absurd({False{} == True{} : Bool}, inv)
    case T.Value{m} T.Value{a} T.Value{b}:
      at_reach.spend_arith(m, sp, a, b, n, inv, fit)

# the split's halves fit the room
def at_reach.lsplit(+lim: T.Lim, +sp: Nat, +hold: Nat, g: {S.has(sp, lim) == True{} : Bool}) -> {S.lim_le(at_reach.lplus(T.Value{sp}, at_reach.lplus(T.half_hi(T.lim_less(T.lim_less(lim, sp), hold)), T.half_lo(T.lim_less(T.lim_less(lim, sp), hold)))), lim) == True{} : Bool}:
  match lim:
    case T.Unlimited{}:
      {==}
    case T.Value{m}:
      %Equal.sym(Nat, Nat.add(Nat.sub(Nat.sub(Nat.sub(m, sp), hold), T.half(Nat.sub(Nat.sub(m, sp), hold))), T.half(Nat.sub(Nat.sub(m, sp), hold))), Nat.sub(Nat.sub(m, sp), hold), at_reach.halves_sum(Nat.sub(Nat.sub(m, sp), hold))) : {Nat.is_le(Nat.add(sp, _), m) == True{} : Bool}
      at_reach.fit_sub(sp, Nat.sub(Nat.sub(m, sp), hold), m, g, at_reach.sub_le(Nat.sub(m, sp), hold))

# a redo of the left child that fits the free budget
def at_reach.lredo_l(+lim: T.Lim, +sp: Nat, +spl: Nat, +x: Nat, +hr: T.Lim, inv: {S.lim_le(at_reach.lplus(T.Value{sp}, at_reach.lplus(T.Value{spl}, hr)), lim) == True{} : Bool}, fit: {T.lim_fits(x, T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.Value{spl}), hr)) == True{} : Bool}) -> {S.lim_le(at_reach.lplus(T.Value{sp}, at_reach.lplus(T.regrant(T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.Value{spl}), hr), spl, x), hr)), lim) == True{} : Bool}:
  match lim hr:
    case T.Unlimited{} v:
      at_reach.le_unl(at_reach.lplus(T.Value{sp}, at_reach.lplus(T.regrant(T.lim_drop(T.lim_drop(T.lim_less(T.Unlimited{}, sp), T.Value{spl}), v), spl, x), v)))
    case T.Value{m} T.Unlimited{}:
      at_reach.absurd({S.lim_le(at_reach.lplus(T.Value{sp}, at_reach.lplus(T.regrant(T.Value{0n}, spl, x), T.Unlimited{})), T.Value{m}) == True{} : Bool}, inv)
    case T.Value{m} T.Value{b}:
      at_reach.redo_arith_l(m, sp, spl, b, x, inv, fit)

# a redo of the right child that fits the free budget
def at_reach.lredo_r(+lim: T.Lim, +sp: Nat, +hl: T.Lim, +spr: Nat, +x: Nat, inv: {S.lim_le(at_reach.lplus(T.Value{sp}, at_reach.lplus(hl, T.Value{spr})), lim) == True{} : Bool}, fit: {T.lim_fits(x, T.lim_drop(T.lim_drop(T.lim_less(lim, sp), hl), T.Value{spr})) == True{} : Bool}) -> {S.lim_le(at_reach.lplus(T.Value{sp}, at_reach.lplus(hl, T.regrant(T.lim_drop(T.lim_drop(T.lim_less(lim, sp), hl), T.Value{spr}), spr, x))), lim) == True{} : Bool}:
  match lim hl:
    case T.Unlimited{} v:
      at_reach.le_unl(at_reach.lplus(T.Value{sp}, at_reach.lplus(v, T.regrant(T.lim_drop(T.lim_drop(T.lim_less(T.Unlimited{}, sp), v), T.Value{spr}), spr, x))))
    case T.Value{m} T.Unlimited{}:
      at_reach.absurd({False{} == True{} : Bool}, inv)
    case T.Value{m} T.Value{a}:
      at_reach.redo_arith_r(m, sp, a, spr, x, inv, fit)

# Scopes
# ------

def at_reach.CC(+x: Bool, +a: Bool, +b: Bool, +c: Bool) -> Type:
  {Nat.add(S.b2n(a), Nat.add(S.b2n(b), S.b2n(c))) == S.b2n(x) : Nat}

# one admitted unit is owned exactly as often as the scope owns it
def at_reach.cell_count(x: Bool, a: Bool, b: Bool, c: Bool, h: {T.cell(x, a, b, c) == True{} : Bool}) -> at_reach.CC(x, a, b, c):
  match x a b c:
    case True{} True{} True{} True{}:
      at_reach.absurd(at_reach.CC(True{}, True{}, True{}, True{}), h)
    case True{} True{} True{} False{}:
      at_reach.absurd(at_reach.CC(True{}, True{}, True{}, False{}), h)
    case True{} True{} False{} True{}:
      at_reach.absurd(at_reach.CC(True{}, True{}, False{}, True{}), h)
    case True{} True{} False{} False{}:
      {==}
    case True{} False{} True{} True{}:
      at_reach.absurd(at_reach.CC(True{}, False{}, True{}, True{}), h)
    case True{} False{} True{} False{}:
      {==}
    case True{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{}:
      at_reach.absurd(at_reach.CC(True{}, False{}, False{}, False{}), h)
    case False{} True{} True{} True{}:
      at_reach.absurd(at_reach.CC(False{}, True{}, True{}, True{}), h)
    case False{} True{} True{} False{}:
      at_reach.absurd(at_reach.CC(False{}, True{}, True{}, False{}), h)
    case False{} True{} False{} True{}:
      at_reach.absurd(at_reach.CC(False{}, True{}, False{}, True{}), h)
    case False{} True{} False{} False{}:
      at_reach.absurd(at_reach.CC(False{}, True{}, False{}, False{}), h)
    case False{} False{} True{} True{}:
      at_reach.absurd(at_reach.CC(False{}, False{}, True{}, True{}), h)
    case False{} False{} True{} False{}:
      at_reach.absurd(at_reach.CC(False{}, False{}, True{}, False{}), h)
    case False{} False{} False{} True{}:
      at_reach.absurd(at_reach.CC(False{}, False{}, False{}, True{}), h)
    case False{} False{} False{} False{}:
      {==}

def at_reach.TC(+s: List<&2, Bool>, +o: List<&2, Bool>, +l: List<&2, Bool>, +r: List<&2, Bool>) -> Type:
  {S.addv(S.counts(o), S.addv(S.counts(l), S.counts(r))) == S.counts(s) : List<&2, Nat>}

# admitted scopes own each unit as often as the scope
def at_reach.tiles_counts(+s: List<&2, Bool>, +o: List<&2, Bool>, +l: List<&2, Bool>, +r: List<&2, Bool>, +h: {T.tiles(s, o, l, r) == True{} : Bool}) -> at_reach.TC(s, o, l, r):
  match s o l r:
    case Nil{} Nil{} Nil{} Nil{}:
      {==}
    case Nil{} Nil{} Nil{} Con{c, ct}:
      at_reach.absurd(at_reach.TC(Nil{}, Nil{}, Nil{}, Con{c, ct}), h)
    case Nil{} Nil{} Con{b, bt} Nil{}:
      at_reach.absurd(at_reach.TC(Nil{}, Nil{}, Con{b, bt}, Nil{}), h)
    case Nil{} Nil{} Con{b, bt} Con{c, ct}:
      at_reach.absurd(at_reach.TC(Nil{}, Nil{}, Con{b, bt}, Con{c, ct}), h)
    case Nil{} Con{a, ot} Nil{} Nil{}:
      at_reach.absurd(at_reach.TC(Nil{}, Con{a, ot}, Nil{}, Nil{}), h)
    case Nil{} Con{a, ot} Nil{} Con{c, ct}:
      at_reach.absurd(at_reach.TC(Nil{}, Con{a, ot}, Nil{}, Con{c, ct}), h)
    case Nil{} Con{a, ot} Con{b, bt} Nil{}:
      at_reach.absurd(at_reach.TC(Nil{}, Con{a, ot}, Con{b, bt}, Nil{}), h)
    case Nil{} Con{a, ot} Con{b, bt} Con{c, ct}:
      at_reach.absurd(at_reach.TC(Nil{}, Con{a, ot}, Con{b, bt}, Con{c, ct}), h)
    case Con{x, xt} Nil{} Nil{} Nil{}:
      at_reach.absurd(at_reach.TC(Con{x, xt}, Nil{}, Nil{}, Nil{}), h)
    case Con{x, xt} Nil{} Nil{} Con{c, ct}:
      at_reach.absurd(at_reach.TC(Con{x, xt}, Nil{}, Nil{}, Con{c, ct}), h)
    case Con{x, xt} Nil{} Con{b, bt} Nil{}:
      at_reach.absurd(at_reach.TC(Con{x, xt}, Nil{}, Con{b, bt}, Nil{}), h)
    case Con{x, xt} Nil{} Con{b, bt} Con{c, ct}:
      at_reach.absurd(at_reach.TC(Con{x, xt}, Nil{}, Con{b, bt}, Con{c, ct}), h)
    case Con{x, xt} Con{a, ot} Nil{} Nil{}:
      at_reach.absurd(at_reach.TC(Con{x, xt}, Con{a, ot}, Nil{}, Nil{}), h)
    case Con{x, xt} Con{a, ot} Nil{} Con{c, ct}:
      at_reach.absurd(at_reach.TC(Con{x, xt}, Con{a, ot}, Nil{}, Con{c, ct}), h)
    case Con{x, xt} Con{a, ot} Con{b, bt} Nil{}:
      at_reach.absurd(at_reach.TC(Con{x, xt}, Con{a, ot}, Con{b, bt}, Nil{}), h)
    case Con{x, xt} Con{a, ot} Con{b, bt} Con{c, ct}:
      +hc = at_reach.and_l(T.cell(x, a, b, c), T.tiles(xt, ot, bt, ct), h)
      +ht = at_reach.and_r(T.cell(x, a, b, c), T.tiles(xt, ot, bt, ct), h)
      %at_reach.cell_count(x, a, b, c, hc) : {Nat.add(S.b2n(a), Nat.add(S.b2n(b), S.b2n(c))) <> S.addv(S.counts(ot), S.addv(S.counts(bt), S.counts(ct))) == _ <> S.counts(xt) : List<&2, Nat>}
      %at_reach.tiles_counts(xt, ot, bt, ct, ht) : {Nat.add(S.b2n(a), Nat.add(S.b2n(b), S.b2n(c))) <> S.addv(S.counts(ot), S.addv(S.counts(bt), S.counts(ct))) == Nat.add(S.b2n(a), Nat.add(S.b2n(b), S.b2n(c))) <> _ : List<&2, Nat>}
      {==}

# The invariant
# -------------

# a node that does not run has children that do not run
def at_reach.RunCond(+st: T.Status, +l: T.Node, +r: T.Node) -> Data:
  match st:
    case T.Running{}:
      Unit
    case T.Finished{}:
      at_reach.And({S.is_running(l) == False{} : Bool}, {S.is_running(r) == False{} : Bool})
    case T.Failed{}:
      at_reach.And({S.is_running(l) == False{} : Bool}, {S.is_running(r) == False{} : Bool})
    case T.Cancelled{}:
      at_reach.And({S.is_running(l) == False{} : Bool}, {S.is_running(r) == False{} : Bool})

# t is well formed with k levels of depth left: a leaf's spend fits its
# limit; a split tiles its scope, keeps RunCond, its spend plus what its
# children hold fits its limit, its children's deadlines are at most its
# own, and its children are Good with one level less
def at_reach.Good(+t: T.Node, +k: Nat) -> Data:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          {S.has(sp, lim) == True{} : Bool}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match k:
            case 0n:
              Empty
            case 1n+q:
              at_reach.And({S.addv(S.counts(own), S.addv(S.counts(T.scope_of(T.info(l))), S.counts(T.scope_of(T.info(r))))) == S.counts(s) : List<&2, Nat>}, at_reach.And(at_reach.RunCond(st, l, r), at_reach.And({S.lim_le(at_reach.lplus(T.Value{sp}, at_reach.lplus(S.held(l), S.held(r))), lim) == True{} : Bool}, at_reach.And({S.lim_le(T.deadline_of(T.info(l)), dl) == True{} : Bool}, at_reach.And({S.lim_le(T.deadline_of(T.info(r)), dl) == True{} : Bool}, at_reach.And(at_reach.Good(l, q), at_reach.Good(r, q)))))))

# m may replace n under a Good parent: same scope, deadline and limit, it
# holds no more of the parent, and it runs only if n ran
def at_reach.Compat(+n: T.Node, +m: T.Node) -> Data:
  at_reach.And({T.scope_of(T.info(m)) == T.scope_of(T.info(n)) : List<&2, Bool>}, at_reach.And({T.deadline_of(T.info(m)) == T.deadline_of(T.info(n)) : T.Lim}, at_reach.And({T.limit_of(T.info(m)) == T.limit_of(T.info(n)) : T.Lim}, at_reach.And({S.lim_le(S.held(m), S.held(n)) == True{} : Bool}, {Bool.or(Bool.not(S.is_running(m)), S.is_running(n)) == True{} : Bool}))))

# a step from t: the new tree is Good, Compat with t, and e nodes larger
def at_reach.Post(+s: T.Step, +t: T.Node, +k: Nat, +e: Nat) -> Data:
  match s:
    case T.Took{n}:
      at_reach.And(at_reach.Good(n, k), at_reach.And(at_reach.Compat(t, n), {T.size(n) == Nat.add(e, T.size(t)) : Nat}))
    case T.Refused{why}:
      Unit

def at_reach.xroom(room: Bool) -> Nat:
  match room:
    case True{}:
      2n
    case False{}:
      0n

# the nodes an op may add
def at_reach.extra(op: T.Op) -> Nat:
  match op:
    case T.OpSplit{own, ls, rs, hold, room, margin}:
      at_reach.xroom(room)
    case T.OpSpend{n}:
      0n
    case T.OpFinish{p}:
      0n
    case T.OpFail{p}:
      0n
    case T.OpCancel{}:
      0n
    case T.OpRedo{side, x}:
      0n

# a reachable tree from init(s, lim, _) under the bounds b
def at_reach.Inv(+t: T.Node, +b: T.Bounds, +s: List<&2, Bool>, +lim: T.Lim) -> Data:
  at_reach.And(at_reach.Good(t, T.bound_depth(b)), at_reach.And({T.scope_of(T.info(t)) == s : List<&2, Bool>}, {T.limit_of(T.info(t)) == lim : T.Lim}))

# Readings of Good
# ----------------

def at_reach.cs(st: T.Status, -lim: T.Lim, -x: Nat) -> {T.charge_st(st, lim, x) == S.held_if(T.running(st), lim, x) : T.Lim}:
  match st:
    case T.Running{}:
      {==}
    case T.Finished{}:
      {==}
    case T.Failed{}:
      {==}
    case T.Cancelled{}:
      {==}

def at_reach.total_eq(+t: T.Node) -> {T.total(t) == S.spent_all(t) : Nat}:
  match t:
    case T.Leaf{i}:
      {==}
    case T.Split{i, own, l, r}:
      %at_reach.total_eq(l) : {T.total(T.Split{i, own, l, r}) == Nat.add(T.spent_of(i), Nat.add(_, S.spent_all(r))) : Nat}
      %at_reach.total_eq(r) : {T.total(T.Split{i, own, l, r}) == Nat.add(T.spent_of(i), Nat.add(T.total(l), _)) : Nat}
      {==}

# the code's charge is the spec's held
def at_reach.charge_held(+t: T.Node) -> {T.charge(t) == S.held(t) : T.Lim}:
  %at_reach.total_eq(t) : {T.charge(t) == S.held_if(T.running(T.st_of(T.info(t))), T.limit_of(T.info(t)), _) : T.Lim}
  at_reach.cs(T.st_of(T.info(t)), T.limit_of(T.info(t)), T.total(t))

def at_reach.hg(rb: Bool, +lim: T.Lim, +x: Nat, f: {S.has(x, lim) == True{} : Bool}) -> {S.lim_le(T.Value{x}, S.held_if(rb, lim, x)) == True{} : Bool}:
  match rb:
    case True{}:
      at_reach.has_le(x, lim, f)
    case False{}:
      at_reach.le_refl(x)

# what a node holds covers what its subtree spent
def at_reach.held_ge_of(+c: T.Node, f: {S.has(S.spent_all(c), T.limit_of(T.info(c))) == True{} : Bool}) -> {S.lim_le(T.Value{S.spent_all(c)}, S.held(c)) == True{} : Bool}:
  at_reach.hg(S.is_running(c), T.limit_of(T.info(c)), S.spent_all(c), f)

# everything a Good subtree spent fits its root's limit
def at_reach.fits_all(+t: T.Node, +k: Nat, +g: at_reach.Good(t, k)) -> {S.has(S.spent_all(t), T.limit_of(T.info(t))) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          g
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match k:
            case 0n:
              match g:
            case 1n+q:
              (tl, g1) = g
              (rc, g2) = g1
              (bu, g3) = g2
              (dl1, g4) = g3
              (dr1, g5) = g4
              (gl, gr) = g5
              at_reach.le_has(S.spent_all(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}), lim, at_reach.bu_mono(sp, lim, T.Value{S.spent_all(l)}, S.held(l), T.Value{S.spent_all(r)}, S.held(r), at_reach.held_ge_of(l, at_reach.fits_all(l, q, gl)), at_reach.held_ge_of(r, at_reach.fits_all(r, q, gr)), bu))

# below a Good node that does not run, nothing runs
def at_reach.quiet_of(+t: T.Node, +k: Nat, +g: at_reach.Good(t, k), e: {S.is_running(t) == False{} : Bool}) -> {S.quiet(t) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              Equal.sym(Bool, True{}, False{}, e)
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              at_reach.absurd_t({S.quiet(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r}) == True{} : Bool}, e)
            case T.Finished{}:
              match k:
                case 0n:
                  match g:
                case 1n+q:
                  (tl, g1) = g
                  (rc, g2) = g1
                  (el, er) = rc
                  (bu, g3) = g2
                  (dl1, g4) = g3
                  (dr1, g5) = g4
                  (gl, gr) = g5
                  at_reach.and_t(S.quiet(l), S.quiet(r), at_reach.quiet_of(l, q, gl, el), at_reach.quiet_of(r, q, gr, er))
            case T.Failed{}:
              match k:
                case 0n:
                  match g:
                case 1n+q:
                  (tl, g1) = g
                  (rc, g2) = g1
                  (el, er) = rc
                  (bu, g3) = g2
                  (dl1, g4) = g3
                  (dr1, g5) = g4
                  (gl, gr) = g5
                  at_reach.and_t(S.quiet(l), S.quiet(r), at_reach.quiet_of(l, q, gl, el), at_reach.quiet_of(r, q, gr, er))
            case T.Cancelled{}:
              match k:
                case 0n:
                  match g:
                case 1n+q:
                  (tl, g1) = g
                  (rc, g2) = g1
                  (el, er) = rc
                  (bu, g3) = g2
                  (dl1, g4) = g3
                  (dr1, g5) = g4
                  (gl, gr) = g5
                  at_reach.and_t(S.quiet(l), S.quiet(r), at_reach.quiet_of(l, q, gl, el), at_reach.quiet_of(r, q, gr, er))

# the children of a Good split are Good
def at_reach.kid_l(+st: T.Status, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +q: Nat, +g: at_reach.Good(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q)) -> at_reach.Good(l, q):
  (tl, g1) = g
  (rc, g2) = g1
  (bu, g3) = g2
  (dl1, g4) = g3
  (dr1, g5) = g4
  (gl, gr) = g5
  gl

def at_reach.kid_r(+st: T.Status, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +q: Nat, +g: at_reach.Good(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q)) -> at_reach.Good(r, q):
  (tl, g1) = g
  (rc, g2) = g1
  (bu, g3) = g2
  (dl1, g4) = g3
  (dr1, g5) = g4
  (gl, gr) = g5
  gr

# the RunCond of a Good split
def at_reach.runc(+st: T.Status, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +q: Nat, +g: at_reach.Good(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q)) -> at_reach.RunCond(st, l, r):
  (tl, g1) = g
  (rc, g2) = g1
  rc

# under a node that does not run, the left child does not run
def at_reach.run_l(+st: T.Status, -l: T.Node, -r: T.Node, rc: at_reach.RunCond(st, l, r), e: {T.running(st) == False{} : Bool}) -> {S.is_running(l) == False{} : Bool}:
  match st:
    case T.Running{}:
      at_reach.absurd_t({S.is_running(l) == False{} : Bool}, e)
    case T.Finished{}:
      (el, er) = rc
      el
    case T.Failed{}:
      (el, er) = rc
      el
    case T.Cancelled{}:
      (el, er) = rc
      el

def at_reach.run_r(+st: T.Status, -l: T.Node, -r: T.Node, rc: at_reach.RunCond(st, l, r), e: {T.running(st) == False{} : Bool}) -> {S.is_running(r) == False{} : Bool}:
  match st:
    case T.Running{}:
      at_reach.absurd_t({S.is_running(r) == False{} : Bool}, e)
    case T.Finished{}:
      (el, er) = rc
      er
    case T.Failed{}:
      (el, er) = rc
      er
    case T.Cancelled{}:
      (el, er) = rc
      er

# a Good split that does not run: nothing below it runs, and both children are Good
def at_reach.orphan_settled(+st: T.Status, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +q: Nat, +g: at_reach.Good(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q), +e: {T.running(st) == False{} : Bool}) -> {Bool.and(S.quiet(l), S.quiet(r)) == True{} : Bool}:
  at_reach.and_t(S.quiet(l), S.quiet(r), at_reach.quiet_of(l, q, at_reach.kid_l(st, s, lim, sp, dl, p, own, l, r, q, g), at_reach.run_l(st, l, r, at_reach.runc(st, s, lim, sp, dl, p, own, l, r, q, g), e)), at_reach.quiet_of(r, q, at_reach.kid_r(st, s, lim, sp, dl, p, own, l, r, q, g), at_reach.run_r(st, l, r, at_reach.runc(st, s, lim, sp, dl, p, own, l, r, q, g), e)))

def at_reach.no_orphan_of(+t: T.Node, +k: Nat, +g: at_reach.Good(t, k)) -> {S.no_orphan(t) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              match k:
                case 0n:
                  match g:
                case 1n+q:
                  at_reach.and_t(S.no_orphan(l), S.no_orphan(r), at_reach.no_orphan_of(l, q, at_reach.kid_l(T.Running{}, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.no_orphan_of(r, q, at_reach.kid_r(T.Running{}, s, lim, sp, dl, p, own, l, r, q, g)))
            case T.Finished{}:
              match k:
                case 0n:
                  match g:
                case 1n+q:
                  at_reach.and_t(Bool.and(S.quiet(l), S.quiet(r)), Bool.and(S.no_orphan(l), S.no_orphan(r)), at_reach.orphan_settled(T.Finished{}, s, lim, sp, dl, p, own, l, r, q, g, {==}), at_reach.and_t(S.no_orphan(l), S.no_orphan(r), at_reach.no_orphan_of(l, q, at_reach.kid_l(T.Finished{}, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.no_orphan_of(r, q, at_reach.kid_r(T.Finished{}, s, lim, sp, dl, p, own, l, r, q, g))))
            case T.Failed{}:
              match k:
                case 0n:
                  match g:
                case 1n+q:
                  at_reach.and_t(Bool.and(S.quiet(l), S.quiet(r)), Bool.and(S.no_orphan(l), S.no_orphan(r)), at_reach.orphan_settled(T.Failed{}, s, lim, sp, dl, p, own, l, r, q, g, {==}), at_reach.and_t(S.no_orphan(l), S.no_orphan(r), at_reach.no_orphan_of(l, q, at_reach.kid_l(T.Failed{}, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.no_orphan_of(r, q, at_reach.kid_r(T.Failed{}, s, lim, sp, dl, p, own, l, r, q, g))))
            case T.Cancelled{}:
              match k:
                case 0n:
                  match g:
                case 1n+q:
                  at_reach.and_t(Bool.and(S.quiet(l), S.quiet(r)), Bool.and(S.no_orphan(l), S.no_orphan(r)), at_reach.orphan_settled(T.Cancelled{}, s, lim, sp, dl, p, own, l, r, q, g, {==}), at_reach.and_t(S.no_orphan(l), S.no_orphan(r), at_reach.no_orphan_of(l, q, at_reach.kid_l(T.Cancelled{}, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.no_orphan_of(r, q, at_reach.kid_r(T.Cancelled{}, s, lim, sp, dl, p, own, l, r, q, g))))

def at_reach.done_of(+t: T.Node, +k: Nat, +g: at_reach.Good(t, k)) -> {S.done_settled(t) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              match k:
                case 0n:
                  match g:
                case 1n+q:
                  at_reach.and_t(S.done_settled(l), S.done_settled(r), at_reach.done_of(l, q, at_reach.kid_l(T.Running{}, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.done_of(r, q, at_reach.kid_r(T.Running{}, s, lim, sp, dl, p, own, l, r, q, g)))
            case T.Finished{}:
              match k:
                case 0n:
                  match g:
                case 1n+q:
                  at_reach.and_t(Bool.and(Bool.not(S.is_running(l)), Bool.not(S.is_running(r))), Bool.and(S.done_settled(l), S.done_settled(r)), at_reach.and_t(Bool.not(S.is_running(l)), Bool.not(S.is_running(r)), at_reach.not_f(S.is_running(l), at_reach.run_l(T.Finished{}, l, r, at_reach.runc(T.Finished{}, s, lim, sp, dl, p, own, l, r, q, g), {==})), at_reach.not_f(S.is_running(r), at_reach.run_r(T.Finished{}, l, r, at_reach.runc(T.Finished{}, s, lim, sp, dl, p, own, l, r, q, g), {==}))), at_reach.and_t(S.done_settled(l), S.done_settled(r), at_reach.done_of(l, q, at_reach.kid_l(T.Finished{}, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.done_of(r, q, at_reach.kid_r(T.Finished{}, s, lim, sp, dl, p, own, l, r, q, g))))
            case T.Failed{}:
              match k:
                case 0n:
                  match g:
                case 1n+q:
                  at_reach.and_t(S.done_settled(l), S.done_settled(r), at_reach.done_of(l, q, at_reach.kid_l(T.Failed{}, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.done_of(r, q, at_reach.kid_r(T.Failed{}, s, lim, sp, dl, p, own, l, r, q, g)))
            case T.Cancelled{}:
              match k:
                case 0n:
                  match g:
                case 1n+q:
                  at_reach.and_t(S.done_settled(l), S.done_settled(r), at_reach.done_of(l, q, at_reach.kid_l(T.Cancelled{}, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.done_of(r, q, at_reach.kid_r(T.Cancelled{}, s, lim, sp, dl, p, own, l, r, q, g)))

def at_reach.dd_of(+t: T.Node, +k: Nat, +g: at_reach.Good(t, k)) -> {S.deadlines_down(t) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match k:
            case 0n:
              match g:
            case 1n+q:
              (tl, g1) = g
              (rc, g2) = g1
              (bu, g3) = g2
              (dl1, g4) = g3
              (dr1, g5) = g4
              (gl, gr) = g5
              at_reach.and_t(Bool.and(S.lim_le(T.deadline_of(T.info(l)), dl), S.lim_le(T.deadline_of(T.info(r)), dl)), Bool.and(S.deadlines_down(l), S.deadlines_down(r)), at_reach.and_t(S.lim_le(T.deadline_of(T.info(l)), dl), S.lim_le(T.deadline_of(T.info(r)), dl), dl1, dr1), at_reach.and_t(S.deadlines_down(l), S.deadlines_down(r), at_reach.dd_of(l, q, gl), at_reach.dd_of(r, q, gr)))

def at_reach.depth_of(+t: T.Node, +k: Nat, +g: at_reach.Good(t, k)) -> {Nat.is_le(S.depth(t), k) == True{} : Bool}:
  match t:
    case T.Leaf{i}:
      at_reach.le0(k)
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match k:
            case 0n:
              match g:
            case 1n+q:
              at_reach.max_le(S.depth(l), S.depth(r), q, at_reach.depth_of(l, q, at_reach.kid_l(st, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.depth_of(r, q, at_reach.kid_r(st, s, lim, sp, dl, p, own, l, r, q, g)))

def at_reach.tile_of(+t: T.Node, +k: Nat, +g: at_reach.Good(t, k)) -> {S.tile(t) == S.counts(T.scope_of(T.info(t))) : List<&2, Nat>}:
  match t:
    case T.Leaf{i}:
      {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match k:
            case 0n:
              match g:
            case 1n+q:
              (tl, g1) = g
              (rc, g2) = g1
              (bu, g3) = g2
              (dl1, g4) = g3
              (dr1, g5) = g4
              (gl, gr) = g5
              %Equal.sym(List<&2, Nat>, S.tile(l), S.counts(T.scope_of(T.info(l))), at_reach.tile_of(l, q, gl)) : {S.addv(S.counts(own), S.addv(_, S.tile(r))) == S.counts(s) : List<&2, Nat>}
              %Equal.sym(List<&2, Nat>, S.tile(r), S.counts(T.scope_of(T.info(r))), at_reach.tile_of(r, q, gr)) : {S.addv(S.counts(own), S.addv(S.counts(T.scope_of(T.info(l))), _)) == S.counts(s) : List<&2, Nat>}
              tl

def at_reach.nodes_size(+t: T.Node) -> {S.nodes(t) == T.size(t) : Nat}:
  match t:
    case T.Leaf{i}:
      {==}
    case T.Split{i, own, l, r}:
      %Equal.sym(Nat, S.nodes(l), T.size(l), at_reach.nodes_size(l)) : {Nat.add(_, 1n+S.nodes(r)) == 1n+Nat.add(T.size(l), T.size(r)) : Nat}
      %Equal.sym(Nat, S.nodes(r), T.size(r), at_reach.nodes_size(r)) : {Nat.add(T.size(l), 1n+_) == 1n+Nat.add(T.size(l), T.size(r)) : Nat}
      at_reach.add_succ(T.size(l), T.size(r))

# Replacing subtrees
# ------------------

def at_reach.held_le_gen(rm: Bool, rn: Bool, +lm: T.Lim, +ln: T.Lim, -sm: Nat, -sn: Nat, el: {lm == ln : T.Lim}, himp: {Bool.or(Bool.not(rm), rn) == True{} : Bool}, hsp: {Bool.or(rm, Nat.is_le(sm, sn)) == True{} : Bool}, hfit: {S.has(sm, lm) == True{} : Bool}) -> {S.lim_le(S.held_if(rm, lm, sm), S.held_if(rn, ln, sn)) == True{} : Bool}:
  match rm rn:
    case True{} True{}:
      %el : {S.lim_le(lm, _) == True{} : Bool}
      at_reach.lim_le_refl(lm)
    case True{} False{}:
      at_reach.absurd({S.lim_le(lm, T.Value{sn}) == True{} : Bool}, himp)
    case False{} True{}:
      %el : {S.lim_le(T.Value{sm}, _) == True{} : Bool}
      at_reach.has_le(sm, lm, hfit)
    case False{} False{}:
      hsp

# a Good m with n's scope, deadline and limit that runs only if n ran and,
# once settled, spent no more than n: m is Compat with n
def at_reach.compat_mk(+n: T.Node, +m: T.Node, +k: Nat, +gm: at_reach.Good(m, k), escope: {T.scope_of(T.info(m)) == T.scope_of(T.info(n)) : List<&2, Bool>}, edl: {T.deadline_of(T.info(m)) == T.deadline_of(T.info(n)) : T.Lim}, +elim: {T.limit_of(T.info(m)) == T.limit_of(T.info(n)) : T.Lim}, +himp: {Bool.or(Bool.not(S.is_running(m)), S.is_running(n)) == True{} : Bool}, hsp: {Bool.or(S.is_running(m), Nat.is_le(S.spent_all(m), S.spent_all(n))) == True{} : Bool}) -> at_reach.Compat(n, m):
  (escope, (edl, (elim, (at_reach.held_le_gen(S.is_running(m), S.is_running(n), T.limit_of(T.info(m)), T.limit_of(T.info(n)), S.spent_all(m), S.spent_all(n), elim, himp, hsp, at_reach.fits_all(m, k, gm)), himp))))

def at_reach.compat_refl(+c: T.Node) -> at_reach.Compat(c, c):
  ({==}, ({==}, ({==}, (at_reach.lim_le_refl(S.held(c)), at_reach.or_not_b(S.is_running(c))))))

def at_reach.rc_keep(+st: T.Status, +l: T.Node, +l2: T.Node, +r: T.Node, +r2: T.Node, rc: at_reach.RunCond(st, l, r), il: {Bool.or(Bool.not(S.is_running(l2)), S.is_running(l)) == True{} : Bool}, ir: {Bool.or(Bool.not(S.is_running(r2)), S.is_running(r)) == True{} : Bool}) -> at_reach.RunCond(st, l2, r2):
  match st:
    case T.Running{}:
      Unit{}
    case T.Finished{}:
      (el, er) = rc
      (at_reach.run_down(S.is_running(l), S.is_running(l2), il, el), at_reach.run_down(S.is_running(r), S.is_running(r2), ir, er))
    case T.Failed{}:
      (el, er) = rc
      (at_reach.run_down(S.is_running(l), S.is_running(l2), il, el), at_reach.run_down(S.is_running(r), S.is_running(r2), ir, er))
    case T.Cancelled{}:
      (el, er) = rc
      (at_reach.run_down(S.is_running(l), S.is_running(l2), il, el), at_reach.run_down(S.is_running(r), S.is_running(r2), ir, er))

def at_reach.rc_stop(+st: T.Status, -l: T.Node, -r: T.Node, el: {S.is_running(l) == False{} : Bool}, er: {S.is_running(r) == False{} : Bool}) -> at_reach.RunCond(st, l, r):
  match st:
    case T.Running{}:
      Unit{}
    case T.Finished{}:
      (el, er)
    case T.Failed{}:
      (el, er)
    case T.Cancelled{}:
      (el, er)

def at_reach.cancel_imp(st: T.Status) -> {Bool.or(Bool.not(T.running(T.cancel_st(st))), T.running(st)) == True{} : Bool}:
  match st:
    case T.Running{}:
      {==}
    case T.Finished{}:
      {==}
    case T.Failed{}:
      {==}
    case T.Cancelled{}:
      {==}

def at_reach.cancel_hsp(st: T.Status, -x: Nat, -y: Nat, h: {Nat.is_le(x, y) == True{} : Bool}) -> {Bool.or(T.running(T.cancel_st(st)), Nat.is_le(x, y)) == True{} : Bool}:
  match st:
    case T.Running{}:
      h
    case T.Finished{}:
      h
    case T.Failed{}:
      h
    case T.Cancelled{}:
      h

def at_reach.settled_sa_le(rl: Bool, rn: Bool, -ll: T.Lim, -ln: T.Lim, -sl: Nat, -sn: Nat, el: {rl == False{} : Bool}, en: {rn == False{} : Bool}, h: {S.lim_le(S.held_if(rn, ln, sn), S.held_if(rl, ll, sl)) == True{} : Bool}) -> {Nat.is_le(sn, sl) == True{} : Bool}:
  match rl rn:
    case True{} True{}:
      at_reach.absurd_t({Nat.is_le(sn, sl) == True{} : Bool}, el)
    case True{} False{}:
      at_reach.absurd_t({Nat.is_le(sn, sl) == True{} : Bool}, el)
    case False{} True{}:
      at_reach.absurd_t({Nat.is_le(sn, sl) == True{} : Bool}, en)
    case False{} False{}:
      h

# a Good split whose children are replaced by Good, Compat ones (its
# status st2 kept by rc2, its patch any) stays Good
def at_reach.repl2(+st2: T.Status, +st: T.Status, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +p2: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +l2: T.Node, +r: T.Node, +r2: T.Node, +q: Nat, +g: at_reach.Good(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q), +gl2: at_reach.Good(l2, q), +gr2: at_reach.Good(r2, q), +cl: at_reach.Compat(l, l2), +cr: at_reach.Compat(r, r2), +rc2: at_reach.RunCond(st2, l2, r2)) -> at_reach.Good(T.Split{T.Info{st2, s, lim, sp, dl, p2}, own, l2, r2}, 1n+q):
  (tl, g1) = g
  (rc, g2) = g1
  (bu, g3) = g2
  (dl1, g4) = g3
  (dr1, g5) = g4
  (csl, cl1) = cl
  (cdll, cl2) = cl1
  (climl, cl3) = cl2
  (chl, cil) = cl3
  (csr, cr1) = cr
  (cdlr, cr2) = cr1
  (climr, cr3) = cr2
  (chr, cir) = cr3
  (at_reach.tr(List<&2, Bool>, T.scope_of(T.info(l)), T.scope_of(T.info(l2)), z => {S.addv(S.counts(own), S.addv(S.counts(z), S.counts(T.scope_of(T.info(r2))))) == S.counts(s) : List<&2, Nat>}, Equal.sym(List<&2, Bool>, T.scope_of(T.info(l2)), T.scope_of(T.info(l)), csl), at_reach.tr(List<&2, Bool>, T.scope_of(T.info(r)), T.scope_of(T.info(r2)), z => {S.addv(S.counts(own), S.addv(S.counts(T.scope_of(T.info(l))), S.counts(z))) == S.counts(s) : List<&2, Nat>}, Equal.sym(List<&2, Bool>, T.scope_of(T.info(r2)), T.scope_of(T.info(r)), csr), tl)), (rc2, (at_reach.bu_mono(sp, lim, S.held(l2), S.held(l), S.held(r2), S.held(r), chl, chr, bu), (at_reach.tr(T.Lim, T.deadline_of(T.info(l)), T.deadline_of(T.info(l2)), z => {S.lim_le(z, dl) == True{} : Bool}, Equal.sym(T.Lim, T.deadline_of(T.info(l2)), T.deadline_of(T.info(l)), cdll), dl1), (at_reach.tr(T.Lim, T.deadline_of(T.info(r)), T.deadline_of(T.info(r2)), z => {S.lim_le(z, dl) == True{} : Bool}, Equal.sym(T.Lim, T.deadline_of(T.info(r2)), T.deadline_of(T.info(r)), cdlr), dr1), (gl2, gr2))))))

def at_reach.hsp_l(+st: T.Status, +sp: Nat, +l: T.Node, +n: T.Node, +r: T.Node, rc: at_reach.RunCond(st, l, r), il: {Bool.or(Bool.not(S.is_running(n)), S.is_running(l)) == True{} : Bool}, h: {S.lim_le(S.held(n), S.held(l)) == True{} : Bool}) -> {Bool.or(T.running(st), Nat.is_le(Nat.add(sp, Nat.add(S.spent_all(n), S.spent_all(r))), Nat.add(sp, Nat.add(S.spent_all(l), S.spent_all(r))))) == True{} : Bool}:
  match st:
    case T.Running{}:
      {==}
    case T.Finished{}:
      (el, er) = rc
      +el2 = el
      at_reach.add_mono_l(sp, Nat.add(S.spent_all(n), S.spent_all(r)), Nat.add(S.spent_all(l), S.spent_all(r)), at_reach.add_mono_r(S.spent_all(n), S.spent_all(l), S.spent_all(r), at_reach.settled_sa_le(S.is_running(l), S.is_running(n), T.limit_of(T.info(l)), T.limit_of(T.info(n)), S.spent_all(l), S.spent_all(n), el2, at_reach.run_down(S.is_running(l), S.is_running(n), il, el2), h)))
    case T.Failed{}:
      (el, er) = rc
      +el2 = el
      at_reach.add_mono_l(sp, Nat.add(S.spent_all(n), S.spent_all(r)), Nat.add(S.spent_all(l), S.spent_all(r)), at_reach.add_mono_r(S.spent_all(n), S.spent_all(l), S.spent_all(r), at_reach.settled_sa_le(S.is_running(l), S.is_running(n), T.limit_of(T.info(l)), T.limit_of(T.info(n)), S.spent_all(l), S.spent_all(n), el2, at_reach.run_down(S.is_running(l), S.is_running(n), il, el2), h)))
    case T.Cancelled{}:
      (el, er) = rc
      +el2 = el
      at_reach.add_mono_l(sp, Nat.add(S.spent_all(n), S.spent_all(r)), Nat.add(S.spent_all(l), S.spent_all(r)), at_reach.add_mono_r(S.spent_all(n), S.spent_all(l), S.spent_all(r), at_reach.settled_sa_le(S.is_running(l), S.is_running(n), T.limit_of(T.info(l)), T.limit_of(T.info(n)), S.spent_all(l), S.spent_all(n), el2, at_reach.run_down(S.is_running(l), S.is_running(n), il, el2), h)))

def at_reach.hsp_r(+st: T.Status, +sp: Nat, +l: T.Node, +n: T.Node, +r: T.Node, rc: at_reach.RunCond(st, l, r), ir: {Bool.or(Bool.not(S.is_running(n)), S.is_running(r)) == True{} : Bool}, h: {S.lim_le(S.held(n), S.held(r)) == True{} : Bool}) -> {Bool.or(T.running(st), Nat.is_le(Nat.add(sp, Nat.add(S.spent_all(l), S.spent_all(n))), Nat.add(sp, Nat.add(S.spent_all(l), S.spent_all(r))))) == True{} : Bool}:
  match st:
    case T.Running{}:
      {==}
    case T.Finished{}:
      (el, er) = rc
      +er2 = er
      at_reach.add_mono_l(sp, Nat.add(S.spent_all(l), S.spent_all(n)), Nat.add(S.spent_all(l), S.spent_all(r)), at_reach.add_mono_l(S.spent_all(l), S.spent_all(n), S.spent_all(r), at_reach.settled_sa_le(S.is_running(r), S.is_running(n), T.limit_of(T.info(r)), T.limit_of(T.info(n)), S.spent_all(r), S.spent_all(n), er2, at_reach.run_down(S.is_running(r), S.is_running(n), ir, er2), h)))
    case T.Failed{}:
      (el, er) = rc
      +er2 = er
      at_reach.add_mono_l(sp, Nat.add(S.spent_all(l), S.spent_all(n)), Nat.add(S.spent_all(l), S.spent_all(r)), at_reach.add_mono_l(S.spent_all(l), S.spent_all(n), S.spent_all(r), at_reach.settled_sa_le(S.is_running(r), S.is_running(n), T.limit_of(T.info(r)), T.limit_of(T.info(n)), S.spent_all(r), S.spent_all(n), er2, at_reach.run_down(S.is_running(r), S.is_running(n), ir, er2), h)))
    case T.Cancelled{}:
      (el, er) = rc
      +er2 = er
      at_reach.add_mono_l(sp, Nat.add(S.spent_all(l), S.spent_all(n)), Nat.add(S.spent_all(l), S.spent_all(r)), at_reach.add_mono_l(S.spent_all(l), S.spent_all(n), S.spent_all(r), at_reach.settled_sa_le(S.is_running(r), S.is_running(n), T.limit_of(T.info(r)), T.limit_of(T.info(n)), S.spent_all(r), S.spent_all(n), er2, at_reach.run_down(S.is_running(r), S.is_running(n), ir, er2), h)))

# projections of Compat
def at_reach.c_held(+n: T.Node, +m: T.Node, +c: at_reach.Compat(n, m)) -> {S.lim_le(S.held(m), S.held(n)) == True{} : Bool}:
  (cs, c1) = c
  (cdl, c2) = c1
  (clim, c3) = c2
  (ch, ci) = c3
  ch

def at_reach.c_run(+n: T.Node, +m: T.Node, +c: at_reach.Compat(n, m)) -> {Bool.or(Bool.not(S.is_running(m)), S.is_running(n)) == True{} : Bool}:
  (cs, c1) = c
  (cdl, c2) = c1
  (clim, c3) = c2
  (ch, ci) = c3
  ci

def at_reach.c_scope(+n: T.Node, +m: T.Node, +c: at_reach.Compat(n, m)) -> {T.scope_of(T.info(m)) == T.scope_of(T.info(n)) : List<&2, Bool>}:
  (cs, c1) = c
  cs

def at_reach.c_lim(+n: T.Node, +m: T.Node, +c: at_reach.Compat(n, m)) -> {T.limit_of(T.info(m)) == T.limit_of(T.info(n)) : T.Lim}:
  (cs, c1) = c
  (cdl, c2) = c1
  (clim, c3) = c2
  clim

# the left child of a Good split replaced by a Good, Compat n
def at_reach.repl_l(+st: T.Status, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +n: T.Node, +r: T.Node, +q: Nat, +e: Nat, +g: at_reach.Good(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q), +gn: at_reach.Good(n, q), +cn: at_reach.Compat(l, n), +sz: {T.size(n) == Nat.add(e, T.size(l)) : Nat}) -> at_reach.Post(T.Took{T.Split{T.Info{st, s, lim, sp, dl, p}, own, n, r}}, T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q, e):
  +gnew = at_reach.repl2(st, st, s, lim, sp, dl, p, p, own, l, n, r, r, q, g, gn, at_reach.kid_r(st, s, lim, sp, dl, p, own, l, r, q, g), cn, at_reach.compat_refl(r), at_reach.rc_keep(st, l, n, r, r, at_reach.runc(st, s, lim, sp, dl, p, own, l, r, q, g), at_reach.c_run(l, n, cn), at_reach.or_not_b(S.is_running(r))))
  (gnew, (at_reach.compat_mk(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, T.Split{T.Info{st, s, lim, sp, dl, p}, own, n, r}, 1n+q, gnew, {==}, {==}, {==}, at_reach.or_not_b(T.running(st)), at_reach.hsp_l(st, sp, l, n, r, at_reach.runc(st, s, lim, sp, dl, p, own, l, r, q, g), at_reach.c_run(l, n, cn), at_reach.c_held(l, n, cn))), at_reach.size_l(e, T.size(l), T.size(n), T.size(r), sz)))

# the right child of a Good split replaced by a Good, Compat n
def at_reach.repl_r(+st: T.Status, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +n: T.Node, +r: T.Node, +q: Nat, +e: Nat, +g: at_reach.Good(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q), +gn: at_reach.Good(n, q), +cn: at_reach.Compat(r, n), +sz: {T.size(n) == Nat.add(e, T.size(r)) : Nat}) -> at_reach.Post(T.Took{T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, n}}, T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q, e):
  +gnew = at_reach.repl2(st, st, s, lim, sp, dl, p, p, own, l, l, r, n, q, g, at_reach.kid_l(st, s, lim, sp, dl, p, own, l, r, q, g), gn, at_reach.compat_refl(l), cn, at_reach.rc_keep(st, l, l, r, n, at_reach.runc(st, s, lim, sp, dl, p, own, l, r, q, g), at_reach.or_not_b(S.is_running(l)), at_reach.c_run(r, n, cn)))
  (gnew, (at_reach.compat_mk(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, n}, 1n+q, gnew, {==}, {==}, {==}, at_reach.or_not_b(T.running(st)), at_reach.hsp_r(st, sp, l, n, r, at_reach.runc(st, s, lim, sp, dl, p, own, l, r, q, g), at_reach.c_run(r, n, cn), at_reach.c_held(r, n, cn))), at_reach.size_r(e, T.size(l), T.size(n), T.size(r), sz)))

# projections of a Post of a taken step
def at_reach.p_good(+n: T.Node, +t: T.Node, +k: Nat, +e: Nat, +ps: at_reach.Post(T.Took{n}, t, k, e)) -> at_reach.Good(n, k):
  (gn, ps1) = ps
  gn

def at_reach.p_compat(+n: T.Node, +t: T.Node, +k: Nat, +e: Nat, +ps: at_reach.Post(T.Took{n}, t, k, e)) -> at_reach.Compat(t, n):
  (gn, ps1) = ps
  (cn, sz) = ps1
  cn

def at_reach.p_size(+n: T.Node, +t: T.Node, +k: Nat, +e: Nat, +ps: at_reach.Post(T.Took{n}, t, k, e)) -> {T.size(n) == Nat.add(e, T.size(t)) : Nat}:
  (gn, ps1) = ps
  (cn, sz) = ps1
  sz

# Cancel
# ------

def at_reach.ca_scope(+t: T.Node) -> {T.scope_of(T.info(T.cancel_all(t))) == T.scope_of(T.info(t)) : List<&2, Bool>}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          {==}

def at_reach.ca_dl(+t: T.Node) -> {T.deadline_of(T.info(T.cancel_all(t))) == T.deadline_of(T.info(t)) : T.Lim}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          {==}

def at_reach.ca_lim(+t: T.Node) -> {T.limit_of(T.info(T.cancel_all(t))) == T.limit_of(T.info(t)) : T.Lim}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          {==}

def at_reach.ca_stop(+t: T.Node) -> {S.is_running(T.cancel_all(t)) == False{} : Bool}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              {==}
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              {==}
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}

def at_reach.ca_spent(+t: T.Node) -> {S.spent_all(T.cancel_all(t)) == S.spent_all(t) : Nat}:
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          %at_reach.ca_spent(l) : {Nat.add(sp, Nat.add(S.spent_all(T.cancel_all(l)), S.spent_all(T.cancel_all(r)))) == Nat.add(sp, Nat.add(_, S.spent_all(r))) : Nat}
          %at_reach.ca_spent(r) : {Nat.add(sp, Nat.add(S.spent_all(T.cancel_all(l)), S.spent_all(T.cancel_all(r)))) == Nat.add(sp, Nat.add(S.spent_all(T.cancel_all(l)), _)) : Nat}
          {==}

def at_reach.ca_size(+t: T.Node) -> {T.size(T.cancel_all(t)) == T.size(t) : Nat}:
  match t:
    case T.Leaf{i}:
      {==}
    case T.Split{i, own, l, r}:
      at_reach.size_kids(T.size(T.cancel_all(l)), T.size(l), T.size(T.cancel_all(r)), T.size(r), at_reach.ca_size(l), at_reach.ca_size(r))

def at_reach.ca_held(+t: T.Node, +k: Nat, +g: at_reach.Good(t, k)) -> {S.lim_le(S.held(T.cancel_all(t)), S.held(t)) == True{} : Bool}:
  %Equal.sym(Bool, S.is_running(T.cancel_all(t)), False{}, at_reach.ca_stop(t)) : {S.lim_le(S.held_if(_, T.limit_of(T.info(T.cancel_all(t))), S.spent_all(T.cancel_all(t))), S.held(t)) == True{} : Bool}
  %Equal.sym(Nat, S.spent_all(T.cancel_all(t)), S.spent_all(t), at_reach.ca_spent(t)) : {S.lim_le(T.Value{_}, S.held(t)) == True{} : Bool}
  at_reach.held_ge_of(t, at_reach.fits_all(t, k, g))

def at_reach.ca_compat(+t: T.Node, +k: Nat, +g: at_reach.Good(t, k)) -> at_reach.Compat(t, T.cancel_all(t)):
  (at_reach.ca_scope(t), (at_reach.ca_dl(t), (at_reach.ca_lim(t), (at_reach.ca_held(t, k, g), at_reach.tr(Bool, False{}, S.is_running(T.cancel_all(t)), z => {Bool.or(Bool.not(z), S.is_running(t)) == True{} : Bool}, Equal.sym(Bool, S.is_running(T.cancel_all(t)), False{}, at_reach.ca_stop(t)), {==})))))

def at_reach.ca_good(+t: T.Node, +k: Nat, +g: at_reach.Good(t, k)) -> at_reach.Good(T.cancel_all(t), k):
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          g
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match k:
            case 0n:
              match g:
            case 1n+q:
              at_reach.repl2(T.cancel_st(st), st, s, lim, sp, dl, p, p, own, l, T.cancel_all(l), r, T.cancel_all(r), q, g, at_reach.ca_good(l, q, at_reach.kid_l(st, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.ca_good(r, q, at_reach.kid_r(st, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.ca_compat(l, q, at_reach.kid_l(st, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.ca_compat(r, q, at_reach.kid_r(st, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.rc_stop(T.cancel_st(st), T.cancel_all(l), T.cancel_all(r), at_reach.ca_stop(l), at_reach.ca_stop(r)))

# Tick
# ----

def at_reach.tick_cut(+c: T.Node, +now: Nat) -> {S.is_running(T.tick(c, now, True{})) == False{} : Bool}:
  match c:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              {==}
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              {==}
            case T.Finished{}:
              {==}
            case T.Failed{}:
              {==}
            case T.Cancelled{}:
              {==}

def at_reach.ti_sp(u: Bool, -st: T.Status, -s: List<&2, Bool>, -lim: T.Lim, -sp: Nat, -dl: T.Lim, -p: List<&2, Maybe<&2, Nat>>) -> {T.spent_of(T.tick_info(u, T.Info{st, s, lim, sp, dl, p})) == sp : Nat}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def at_reach.tick_spent(+c: T.Node, +now: Nat, +u: Bool) -> {S.spent_all(T.tick(c, now, u)) == S.spent_all(c) : Nat}:
  match c:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          at_reach.ti_sp(Bool.or(u, T.expired(T.Info{st, s, lim, sp, dl, p}, now)), st, s, lim, sp, dl, p)
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          %at_reach.ti_sp(Bool.or(u, T.expired(T.Info{st, s, lim, sp, dl, p}, now)), st, s, lim, sp, dl, p) : {S.spent_all(T.tick(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, now, u)) == Nat.add(_, Nat.add(S.spent_all(l), S.spent_all(r))) : Nat}
          %at_reach.tick_spent(l, now, Bool.or(u, T.expired(T.Info{st, s, lim, sp, dl, p}, now))) : {S.spent_all(T.tick(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, now, u)) == Nat.add(T.spent_of(T.tick_info(Bool.or(u, T.expired(T.Info{st, s, lim, sp, dl, p}, now)), T.Info{st, s, lim, sp, dl, p})), Nat.add(_, S.spent_all(r))) : Nat}
          %at_reach.tick_spent(r, now, Bool.or(u, T.expired(T.Info{st, s, lim, sp, dl, p}, now))) : {S.spent_all(T.tick(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, now, u)) == Nat.add(T.spent_of(T.tick_info(Bool.or(u, T.expired(T.Info{st, s, lim, sp, dl, p}, now)), T.Info{st, s, lim, sp, dl, p})), Nat.add(S.spent_all(T.tick(l, now, Bool.or(u, T.expired(T.Info{st, s, lim, sp, dl, p}, now)))), _)) : Nat}
          {==}

def at_reach.tleaf(u: Bool, +st: T.Status, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +k: Nat, +g: {S.has(sp, lim) == True{} : Bool}) -> at_reach.Post(T.Took{T.Leaf{T.tick_info(u, T.Info{st, s, lim, sp, dl, p})}}, T.Leaf{T.Info{st, s, lim, sp, dl, p}}, k, 0n):
  match u:
    case True{}:
      (g, (at_reach.compat_mk(T.Leaf{T.Info{st, s, lim, sp, dl, p}}, T.Leaf{T.Info{T.cancel_st(st), s, lim, sp, dl, p}}, k, g, {==}, {==}, {==}, at_reach.cancel_imp(st), at_reach.cancel_hsp(st, sp, sp, at_reach.le_refl(sp))), {==}))
    case False{}:
      (g, (at_reach.compat_mk(T.Leaf{T.Info{st, s, lim, sp, dl, p}}, T.Leaf{T.Info{st, s, lim, sp, dl, p}}, k, g, {==}, {==}, {==}, at_reach.or_not_b(T.running(st)), at_reach.or_r(T.running(st), Nat.is_le(sp, sp), at_reach.le_refl(sp))), {==}))

def at_reach.tsplit(u: Bool, +st: T.Status, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +q: Nat, +now: Nat, +g: at_reach.Good(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q), +pl: at_reach.Post(T.Took{T.tick(l, now, u)}, l, q, 0n), +pr: at_reach.Post(T.Took{T.tick(r, now, u)}, r, q, 0n)) -> at_reach.Post(T.Took{T.Split{T.tick_info(u, T.Info{st, s, lim, sp, dl, p}), own, T.tick(l, now, u), T.tick(r, now, u)}}, T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q, 0n):
  match u:
    case True{}:
      +gnew = at_reach.repl2(T.cancel_st(st), st, s, lim, sp, dl, p, p, own, l, T.tick(l, now, True{}), r, T.tick(r, now, True{}), q, g, at_reach.p_good(T.tick(l, now, True{}), l, q, 0n, pl), at_reach.p_good(T.tick(r, now, True{}), r, q, 0n, pr), at_reach.p_compat(T.tick(l, now, True{}), l, q, 0n, pl), at_reach.p_compat(T.tick(r, now, True{}), r, q, 0n, pr), at_reach.rc_stop(T.cancel_st(st), T.tick(l, now, True{}), T.tick(r, now, True{}), at_reach.tick_cut(l, now), at_reach.tick_cut(r, now)))
      (gnew, (at_reach.compat_mk(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, T.Split{T.Info{T.cancel_st(st), s, lim, sp, dl, p}, own, T.tick(l, now, True{}), T.tick(r, now, True{})}, 1n+q, gnew, {==}, {==}, {==}, at_reach.cancel_imp(st), at_reach.cancel_hsp(st, Nat.add(sp, Nat.add(S.spent_all(T.tick(l, now, True{})), S.spent_all(T.tick(r, now, True{})))), Nat.add(sp, Nat.add(S.spent_all(l), S.spent_all(r))), at_reach.le_kids(sp, S.spent_all(T.tick(l, now, True{})), S.spent_all(l), S.spent_all(T.tick(r, now, True{})), S.spent_all(r), at_reach.tick_spent(l, now, True{}), at_reach.tick_spent(r, now, True{})))), at_reach.size_kids(T.size(T.tick(l, now, True{})), T.size(l), T.size(T.tick(r, now, True{})), T.size(r), at_reach.p_size(T.tick(l, now, True{}), l, q, 0n, pl), at_reach.p_size(T.tick(r, now, True{}), r, q, 0n, pr))))
    case False{}:
      +gnew = at_reach.repl2(st, st, s, lim, sp, dl, p, p, own, l, T.tick(l, now, False{}), r, T.tick(r, now, False{}), q, g, at_reach.p_good(T.tick(l, now, False{}), l, q, 0n, pl), at_reach.p_good(T.tick(r, now, False{}), r, q, 0n, pr), at_reach.p_compat(T.tick(l, now, False{}), l, q, 0n, pl), at_reach.p_compat(T.tick(r, now, False{}), r, q, 0n, pr), at_reach.rc_keep(st, l, T.tick(l, now, False{}), r, T.tick(r, now, False{}), at_reach.runc(st, s, lim, sp, dl, p, own, l, r, q, g), at_reach.c_run(l, T.tick(l, now, False{}), at_reach.p_compat(T.tick(l, now, False{}), l, q, 0n, pl)), at_reach.c_run(r, T.tick(r, now, False{}), at_reach.p_compat(T.tick(r, now, False{}), r, q, 0n, pr))))
      (gnew, (at_reach.compat_mk(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, T.Split{T.Info{st, s, lim, sp, dl, p}, own, T.tick(l, now, False{}), T.tick(r, now, False{})}, 1n+q, gnew, {==}, {==}, {==}, at_reach.or_not_b(T.running(st)), at_reach.or_r(T.running(st), Nat.is_le(Nat.add(sp, Nat.add(S.spent_all(T.tick(l, now, False{})), S.spent_all(T.tick(r, now, False{})))), Nat.add(sp, Nat.add(S.spent_all(l), S.spent_all(r)))), at_reach.le_kids(sp, S.spent_all(T.tick(l, now, False{})), S.spent_all(l), S.spent_all(T.tick(r, now, False{})), S.spent_all(r), at_reach.tick_spent(l, now, False{}), at_reach.tick_spent(r, now, False{})))), at_reach.size_kids(T.size(T.tick(l, now, False{})), T.size(l), T.size(T.tick(r, now, False{})), T.size(r), at_reach.p_size(T.tick(l, now, False{}), l, q, 0n, pl), at_reach.p_size(T.tick(r, now, False{}), r, q, 0n, pr))))

# a tick keeps Good and is Compat with the tree it ticks
def at_reach.tick_lem(+t: T.Node, +now: Nat, +cut: Bool, +k: Nat, +g: at_reach.Good(t, k)) -> at_reach.Post(T.Took{T.tick(t, now, cut)}, t, k, 0n):
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          at_reach.tleaf(Bool.or(cut, T.expired(T.Info{st, s, lim, sp, dl, p}, now)), st, s, lim, sp, dl, p, k, g)
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match k:
            case 0n:
              match g:
            case 1n+q:
              at_reach.tsplit(Bool.or(cut, T.expired(T.Info{st, s, lim, sp, dl, p}, now)), st, s, lim, sp, dl, p, own, l, r, q, now, g, at_reach.tick_lem(l, now, Bool.or(cut, T.expired(T.Info{st, s, lim, sp, dl, p}, now)), q, at_reach.kid_l(st, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.tick_lem(r, now, Bool.or(cut, T.expired(T.Info{st, s, lim, sp, dl, p}, now)), q, at_reach.kid_r(st, s, lim, sp, dl, p, own, l, r, q, g)))

# Local ops
# ---------

def at_reach.sp_budget(ok: Bool, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat, +margin: Nat, +q: Nat, +g: {S.has(sp, lim) == True{} : Bool}, et: at_reach.TC(s, own, ls, rs)) -> at_reach.Post(T.split_budget(ok, T.Info{T.Running{}, s, lim, sp, dl, p}, own, ls, rs, hold, margin), T.Leaf{T.Info{T.Running{}, s, lim, sp, dl, p}}, 1n+q, 2n):
  match ok:
    case True{}:
      ((et, (Unit{}, (at_reach.lsplit(lim, sp, hold, g), (at_reach.dl_less(dl, margin), (at_reach.dl_less(dl, margin), (at_reach.has0(T.half_hi(T.lim_less(T.lim_less(lim, sp), hold))), at_reach.has0(T.half_lo(T.lim_less(T.lim_less(lim, sp), hold))))))))), (({==}, ({==}, ({==}, (at_reach.lim_le_refl(lim), {==})))), {==}))
    case False{}:
      Unit{}

def at_reach.sp_scopes(ok: Bool, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat, +margin: Nat, +q: Nat, +g: {S.has(sp, lim) == True{} : Bool}, +eok: {ok == Bool.and(T.tiles(s, own, ls, rs), Bool.and(T.any(ls), T.any(rs))) : Bool}) -> at_reach.Post(T.split_scopes(ok, T.Info{T.Running{}, s, lim, sp, dl, p}, own, ls, rs, hold, margin), T.Leaf{T.Info{T.Running{}, s, lim, sp, dl, p}}, 1n+q, 2n):
  match ok:
    case True{}:
      at_reach.sp_budget(T.lim_fits(Nat.add(hold, 2n), T.lim_less(lim, sp)), s, lim, sp, dl, p, own, ls, rs, hold, margin, q, g, at_reach.tiles_counts(s, own, ls, rs, at_reach.and_l(T.tiles(s, own, ls, rs), Bool.and(T.any(ls), T.any(rs)), Equal.sym(Bool, True{}, Bool.and(T.tiles(s, own, ls, rs), Bool.and(T.any(ls), T.any(rs))), eok))))
    case False{}:
      Unit{}

def at_reach.local_split(+t: T.Node, +k: Nat, +room: Bool, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat, +margin: Nat, +g: at_reach.Good(t, k)) -> at_reach.Post(T.local(T.OpSplit{own, ls, rs, hold, room, margin}, t, k), t, k, at_reach.xroom(room)):
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              match k:
                case 0n:
                  Unit{}
                case 1n+q:
                  match room:
                    case True{}:
                      at_reach.sp_scopes(Bool.and(T.tiles(s, own, ls, rs), Bool.and(T.any(ls), T.any(rs))), s, lim, sp, dl, p, own, ls, rs, hold, margin, q, g, {==})
                    case False{}:
                      Unit{}
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}
    case T.Split{i, o2, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              Unit{}
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}

def at_reach.spend_leaf(ok: Bool, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +n: Nat, +k: Nat, +g: {S.has(sp, lim) == True{} : Bool}, +eok: {ok == T.lim_fits(n, T.lim_less(lim, sp)) : Bool}) -> at_reach.Post(T.spend_fits(ok, T.Leaf{T.Info{T.Running{}, s, lim, sp, dl, p}}, n), T.Leaf{T.Info{T.Running{}, s, lim, sp, dl, p}}, k, 0n):
  match ok:
    case True{}:
      +gn = at_reach.lleaf(lim, sp, n, g, Equal.sym(Bool, True{}, T.lim_fits(n, T.lim_less(lim, sp)), eok))
      (gn, (at_reach.compat_mk(T.Leaf{T.Info{T.Running{}, s, lim, sp, dl, p}}, T.Leaf{T.Info{T.Running{}, s, lim, Nat.add(sp, n), dl, p}}, k, gn, {==}, {==}, {==}, {==}, {==}), {==}))
    case False{}:
      Unit{}

def at_reach.spend_split(ok: Bool, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +n: Nat, +q: Nat, +g: at_reach.Good(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r}, 1n+q), +eok: {ok == T.lim_fits(n, T.free(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r})) : Bool}) -> at_reach.Post(T.spend_fits(ok, T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r}, n), T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r}, 1n+q, 0n):
  match ok:
    case True{}:
      (tl, g1) = g
      (rc, g2) = g1
      (bu, g3) = g2
      (dl1, g4) = g3
      (dr1, g5) = g4
      (gl, gr) = g5
      +fit1 = at_reach.tr(T.Lim, T.charge(l), S.held(l), z => {T.lim_fits(n, T.lim_drop(T.lim_drop(T.lim_less(lim, sp), z), T.charge(r))) == True{} : Bool}, at_reach.charge_held(l), Equal.sym(Bool, True{}, T.lim_fits(n, T.free(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r})), eok))
      +fit2 = at_reach.tr(T.Lim, T.charge(r), S.held(r), z => {T.lim_fits(n, T.lim_drop(T.lim_drop(T.lim_less(lim, sp), S.held(l)), z)) == True{} : Bool}, at_reach.charge_held(r), fit1)
      +gn = {(tl, (Unit{}, (at_reach.lspend(lim, sp, n, S.held(l), S.held(r), bu, fit2), (dl1, (dr1, (gl, gr)))))) : at_reach.Good(T.Split{T.Info{T.Running{}, s, lim, Nat.add(sp, n), dl, p}, own, l, r}, 1n+q)}
      (gn, (at_reach.compat_mk(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r}, T.Split{T.Info{T.Running{}, s, lim, Nat.add(sp, n), dl, p}, own, l, r}, 1n+q, gn, {==}, {==}, {==}, {==}, {==}), {==}))
    case False{}:
      Unit{}

def at_reach.local_spend(+t: T.Node, +n: Nat, +k: Nat, +g: at_reach.Good(t, k)) -> at_reach.Post(T.local(T.OpSpend{n}, t, k), t, k, 0n):
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              at_reach.spend_leaf(T.lim_fits(n, T.lim_less(lim, sp)), s, lim, sp, dl, p, n, k, g, {==})
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              match k:
                case 0n:
                  match g:
                case 1n+q:
                  at_reach.spend_split(T.lim_fits(n, T.free(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r})), s, lim, sp, dl, p, own, l, r, n, q, g, {==})
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}

def at_reach.fin_split(ok: Bool, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +pq: List<&2, Maybe<&2, Nat>>, +q: Nat, +g: at_reach.Good(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r}, 1n+q), +eok: {ok == Bool.and(Bool.not(T.running(T.st_of(T.info(l)))), Bool.not(T.running(T.st_of(T.info(r))))) : Bool}) -> at_reach.Post(T.finish_settled(ok, T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r, pq), T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r}, 1n+q, 0n):
  match ok:
    case True{}:
      +h = Equal.sym(Bool, True{}, Bool.and(Bool.not(S.is_running(l)), Bool.not(S.is_running(r))), eok)
      +gn = at_reach.repl2(T.Finished{}, T.Running{}, s, lim, sp, dl, p, pq, own, l, l, r, r, q, g, at_reach.kid_l(T.Running{}, s, lim, sp, dl, p, own, l, r, q, g), at_reach.kid_r(T.Running{}, s, lim, sp, dl, p, own, l, r, q, g), at_reach.compat_refl(l), at_reach.compat_refl(r), (at_reach.not_t(S.is_running(l), at_reach.and_l(Bool.not(S.is_running(l)), Bool.not(S.is_running(r)), h)), at_reach.not_t(S.is_running(r), at_reach.and_r(Bool.not(S.is_running(l)), Bool.not(S.is_running(r)), h))))
      (gn, (at_reach.compat_mk(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r}, T.Split{T.Info{T.Finished{}, s, lim, sp, dl, pq}, own, l, r}, 1n+q, gn, {==}, {==}, {==}, {==}, at_reach.le_refl(Nat.add(sp, Nat.add(S.spent_all(l), S.spent_all(r))))), {==}))
    case False{}:
      Unit{}

def at_reach.local_finish(+t: T.Node, +pq: List<&2, Maybe<&2, Nat>>, +k: Nat, +g: at_reach.Good(t, k)) -> at_reach.Post(T.local(T.OpFinish{pq}, t, k), t, k, 0n):
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              (g, (at_reach.compat_mk(T.Leaf{T.Info{T.Running{}, s, lim, sp, dl, p}}, T.Leaf{T.Info{T.Finished{}, s, lim, sp, dl, pq}}, k, g, {==}, {==}, {==}, {==}, at_reach.le_refl(sp)), {==}))
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              match k:
                case 0n:
                  match g:
                case 1n+q:
                  at_reach.fin_split(Bool.and(Bool.not(T.running(T.st_of(T.info(l)))), Bool.not(T.running(T.st_of(T.info(r))))), s, lim, sp, dl, p, own, l, r, pq, q, g, {==})
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}

def at_reach.local_fail(+t: T.Node, +pq: List<&2, Maybe<&2, Nat>>, +k: Nat, +g: at_reach.Good(t, k)) -> at_reach.Post(T.local(T.OpFail{pq}, t, k), t, k, 0n):
  match t:
    case T.Leaf{i}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              (g, (at_reach.compat_mk(T.Leaf{T.Info{T.Running{}, s, lim, sp, dl, p}}, T.Leaf{T.Info{T.Failed{}, s, lim, sp, dl, pq}}, k, g, {==}, {==}, {==}, {==}, at_reach.le_refl(sp)), {==}))
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}
    case T.Split{i, own, l, r}:
      match i:
        case T.Info{st, s, lim, sp, dl, p}:
          match st:
            case T.Running{}:
              match k:
                case 0n:
                  match g:
                case 1n+q:
                  +gn = at_reach.repl2(T.Failed{}, T.Running{}, s, lim, sp, dl, p, pq, own, l, T.cancel_all(l), r, T.cancel_all(r), q, g, at_reach.ca_good(l, q, at_reach.kid_l(T.Running{}, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.ca_good(r, q, at_reach.kid_r(T.Running{}, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.ca_compat(l, q, at_reach.kid_l(T.Running{}, s, lim, sp, dl, p, own, l, r, q, g)), at_reach.ca_compat(r, q, at_reach.kid_r(T.Running{}, s, lim, sp, dl, p, own, l, r, q, g)), (at_reach.ca_stop(l), at_reach.ca_stop(r)))
                  (gn, (at_reach.compat_mk(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, r}, T.Split{T.Info{T.Failed{}, s, lim, sp, dl, pq}, own, T.cancel_all(l), T.cancel_all(r)}, 1n+q, gn, {==}, {==}, {==}, {==}, at_reach.le_kids(sp, S.spent_all(T.cancel_all(l)), S.spent_all(l), S.spent_all(T.cancel_all(r)), S.spent_all(r), at_reach.ca_spent(l), at_reach.ca_spent(r))), at_reach.size_kids(T.size(T.cancel_all(l)), T.size(l), T.size(T.cancel_all(r)), T.size(r), at_reach.ca_size(l), at_reach.ca_size(r))))
            case T.Finished{}:
              Unit{}
            case T.Failed{}:
              Unit{}
            case T.Cancelled{}:
              Unit{}

# a redo of the left child, a failed or cancelled leaf, under a running split
def at_reach.redo_l(ok: Bool, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +stl: T.Status, +sl: List<&2, Bool>, +liml: T.Lim, +spl: Nat, +dll: T.Lim, +pl: List<&2, Maybe<&2, Nat>>, +r: T.Node, +x: Nat, +q: Nat, +tl: {S.addv(S.counts(own), S.addv(S.counts(sl), S.counts(T.scope_of(T.info(r))))) == S.counts(s) : List<&2, Nat>}, +bu: {S.lim_le(at_reach.lplus(T.Value{sp}, at_reach.lplus(T.Value{spl}, S.held(r))), lim) == True{} : Bool}, +dl1: {S.lim_le(dll, dl) == True{} : Bool}, +dr1: {S.lim_le(T.deadline_of(T.info(r)), dl) == True{} : Bool}, +gr: at_reach.Good(r, q), +eok: {ok == T.lim_fits(x, T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.Value{spl}), T.charge(r))) : Bool}) -> at_reach.Post(T.redo_budget(ok, T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.Value{spl}), T.charge(r)), T.Info{T.Running{}, s, lim, sp, dl, p}, own, T.GoL{}, x, T.Leaf{T.Info{stl, sl, liml, spl, dll, pl}}, r), T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, T.Leaf{T.Info{stl, sl, liml, spl, dll, pl}}, r}, 1n+q, 0n):
  match ok:
    case True{}:
      +fit1 = at_reach.tr(T.Lim, T.charge(r), S.held(r), z => {T.lim_fits(x, T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.Value{spl}), z)) == True{} : Bool}, at_reach.charge_held(r), Equal.sym(Bool, True{}, T.lim_fits(x, T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.Value{spl}), T.charge(r))), eok))
      +b2 = at_reach.tr(T.Lim, S.held(r), T.charge(r), z => {S.lim_le(at_reach.lplus(T.Value{sp}, at_reach.lplus(T.regrant(T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.Value{spl}), z), spl, x), S.held(r))), lim) == True{} : Bool}, Equal.sym(T.Lim, T.charge(r), S.held(r), at_reach.charge_held(r)), at_reach.lredo_l(lim, sp, spl, x, S.held(r), bu, fit1))
      +gn = {(tl, (Unit{}, (b2, (dl1, (dr1, (at_reach.regrant_has(T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.Value{spl}), T.charge(r)), spl, x), gr)))))) : at_reach.Good(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, T.Leaf{T.Info{T.Running{}, sl, T.regrant(T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.Value{spl}), T.charge(r)), spl, x), spl, dll, pl}}, r}, 1n+q)}
      (gn, (at_reach.compat_mk(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, T.Leaf{T.Info{stl, sl, liml, spl, dll, pl}}, r}, T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, T.Leaf{T.Info{T.Running{}, sl, T.regrant(T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.Value{spl}), T.charge(r)), spl, x), spl, dll, pl}}, r}, 1n+q, gn, {==}, {==}, {==}, {==}, {==}), {==}))
    case False{}:
      Unit{}

# a redo of the right child, a failed or cancelled leaf, under a running split
def at_reach.redo_r(ok: Bool, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +str: T.Status, +sr: List<&2, Bool>, +limr: T.Lim, +spr: Nat, +dlr: T.Lim, +pr: List<&2, Maybe<&2, Nat>>, +x: Nat, +q: Nat, +tl: {S.addv(S.counts(own), S.addv(S.counts(T.scope_of(T.info(l))), S.counts(sr))) == S.counts(s) : List<&2, Nat>}, +bu: {S.lim_le(at_reach.lplus(T.Value{sp}, at_reach.lplus(S.held(l), T.Value{spr})), lim) == True{} : Bool}, +dl1: {S.lim_le(T.deadline_of(T.info(l)), dl) == True{} : Bool}, +dr1: {S.lim_le(dlr, dl) == True{} : Bool}, +gl: at_reach.Good(l, q), +eok: {ok == T.lim_fits(x, T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.charge(l)), T.Value{spr})) : Bool}) -> at_reach.Post(T.redo_budget(ok, T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.charge(l)), T.Value{spr}), T.Info{T.Running{}, s, lim, sp, dl, p}, own, T.GoR{}, x, l, T.Leaf{T.Info{str, sr, limr, spr, dlr, pr}}), T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, T.Leaf{T.Info{str, sr, limr, spr, dlr, pr}}}, 1n+q, 0n):
  match ok:
    case True{}:
      +fit1 = at_reach.tr(T.Lim, T.charge(l), S.held(l), z => {T.lim_fits(x, T.lim_drop(T.lim_drop(T.lim_less(lim, sp), z), T.Value{spr})) == True{} : Bool}, at_reach.charge_held(l), Equal.sym(Bool, True{}, T.lim_fits(x, T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.charge(l)), T.Value{spr})), eok))
      +b2 = at_reach.tr(T.Lim, S.held(l), T.charge(l), z => {S.lim_le(at_reach.lplus(T.Value{sp}, at_reach.lplus(S.held(l), T.regrant(T.lim_drop(T.lim_drop(T.lim_less(lim, sp), z), T.Value{spr}), spr, x))), lim) == True{} : Bool}, Equal.sym(T.Lim, T.charge(l), S.held(l), at_reach.charge_held(l)), at_reach.lredo_r(lim, sp, S.held(l), spr, x, bu, fit1))
      +gn = {(tl, (Unit{}, (b2, (dl1, (dr1, (gl, at_reach.regrant_has(T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.charge(l)), T.Value{spr}), spr, x))))))) : at_reach.Good(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, T.Leaf{T.Info{T.Running{}, sr, T.regrant(T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.charge(l)), T.Value{spr}), spr, x), spr, dlr, pr}}}, 1n+q)}
      (gn, (at_reach.compat_mk(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, T.Leaf{T.Info{str, sr, limr, spr, dlr, pr}}}, T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, T.Leaf{T.Info{T.Running{}, sr, T.regrant(T.lim_drop(T.lim_drop(T.lim_less(lim, sp), T.charge(l)), T.Value{spr}), spr, x), spr, dlr, pr}}}, 1n+q, gn, {==}, {==}, {==}, {==}, {==}), {==}))
    case False{}:
      Unit{}

def at_reach.local_redo(+side: T.Dir, +t: T.Node, +x: Nat, +k: Nat, +g: at_reach.Good(t, k)) -> at_reach.Post(T.local(T.OpRedo{side, x}, t, k), t, k, 0n):
  match side:
    case T.GoL{}:
      match t:
        case T.Leaf{i}:
          match i:
            case T.Info{st, s, lim, sp, dl, p}:
              match st:
                case T.Running{}:
                  Unit{}
                case T.Finished{}:
                  Unit{}
                case T.Failed{}:
                  Unit{}
                case T.Cancelled{}:
                  Unit{}
        case T.Split{i, own, l, r}:
          match i:
            case T.Info{st, s, lim, sp, dl, p}:
              match st:
                case T.Running{}:
                  match l:
                    case T.Leaf{il}:
                      match il:
                        case T.Info{stl, sl, liml, spl, dll, pl}:
                          match stl:
                            case T.Running{}:
                              Unit{}
                            case T.Finished{}:
                              Unit{}
                            case T.Failed{}:
                              match k:
                                case 0n:
                                  match g:
                                case 1n+q:
                                  (tl, g1) = g
                                  (rc, g2) = g1
                                  (bu, g3) = g2
                                  (dl1, g4) = g3
                                  (dr1, g5) = g4
                                  (gl, gr) = g5
                                  at_reach.redo_l(T.lim_fits(x, T.free(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, T.Leaf{T.Info{T.Failed{}, sl, liml, spl, dll, pl}}, r})), s, lim, sp, dl, p, own, T.Failed{}, sl, liml, spl, dll, pl, r, x, q, tl, bu, dl1, dr1, gr, {==})
                            case T.Cancelled{}:
                              match k:
                                case 0n:
                                  match g:
                                case 1n+q:
                                  (tl, g1) = g
                                  (rc, g2) = g1
                                  (bu, g3) = g2
                                  (dl1, g4) = g3
                                  (dr1, g5) = g4
                                  (gl, gr) = g5
                                  at_reach.redo_l(T.lim_fits(x, T.free(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, T.Leaf{T.Info{T.Cancelled{}, sl, liml, spl, dll, pl}}, r})), s, lim, sp, dl, p, own, T.Cancelled{}, sl, liml, spl, dll, pl, r, x, q, tl, bu, dl1, dr1, gr, {==})
                    case T.Split{il, ol, ll, lr}:
                      Unit{}
                case T.Finished{}:
                  Unit{}
                case T.Failed{}:
                  Unit{}
                case T.Cancelled{}:
                  Unit{}
    case T.GoR{}:
      match t:
        case T.Leaf{i}:
          match i:
            case T.Info{st, s, lim, sp, dl, p}:
              match st:
                case T.Running{}:
                  Unit{}
                case T.Finished{}:
                  Unit{}
                case T.Failed{}:
                  Unit{}
                case T.Cancelled{}:
                  Unit{}
        case T.Split{i, own, l, r}:
          match i:
            case T.Info{st, s, lim, sp, dl, p}:
              match st:
                case T.Running{}:
                  match r:
                    case T.Leaf{ir}:
                      match ir:
                        case T.Info{str, sr, limr, spr, dlr, pr}:
                          match str:
                            case T.Running{}:
                              Unit{}
                            case T.Finished{}:
                              Unit{}
                            case T.Failed{}:
                              match k:
                                case 0n:
                                  match g:
                                case 1n+q:
                                  (tl, g1) = g
                                  (rc, g2) = g1
                                  (bu, g3) = g2
                                  (dl1, g4) = g3
                                  (dr1, g5) = g4
                                  (gl, gr) = g5
                                  at_reach.redo_r(T.lim_fits(x, T.free(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, T.Leaf{T.Info{T.Failed{}, sr, limr, spr, dlr, pr}}})), s, lim, sp, dl, p, own, l, T.Failed{}, sr, limr, spr, dlr, pr, x, q, tl, bu, dl1, dr1, gl, {==})
                            case T.Cancelled{}:
                              match k:
                                case 0n:
                                  match g:
                                case 1n+q:
                                  (tl, g1) = g
                                  (rc, g2) = g1
                                  (bu, g3) = g2
                                  (dl1, g4) = g3
                                  (dr1, g5) = g4
                                  (gl, gr) = g5
                                  at_reach.redo_r(T.lim_fits(x, T.free(T.Split{T.Info{T.Running{}, s, lim, sp, dl, p}, own, l, T.Leaf{T.Info{T.Cancelled{}, sr, limr, spr, dlr, pr}}})), s, lim, sp, dl, p, own, l, T.Cancelled{}, sr, limr, spr, dlr, pr, x, q, tl, bu, dl1, dr1, gl, {==})
                    case T.Split{ir, orr, rl, rr}:
                      Unit{}
                case T.Finished{}:
                  Unit{}
                case T.Failed{}:
                  Unit{}
                case T.Cancelled{}:
                  Unit{}

# every op at the node it names keeps Good, is Compat, and adds extra(op) nodes
def at_reach.local_post(+op: T.Op, +t: T.Node, +k: Nat, +g: at_reach.Good(t, k)) -> at_reach.Post(T.local(op, t, k), t, k, at_reach.extra(op)):
  match op:
    case T.OpSplit{own, ls, rs, hold, room, margin}:
      at_reach.local_split(t, k, room, own, ls, rs, hold, margin, g)
    case T.OpSpend{n}:
      at_reach.local_spend(t, n, k, g)
    case T.OpFinish{pq}:
      at_reach.local_finish(t, pq, k, g)
    case T.OpFail{pq}:
      at_reach.local_fail(t, pq, k, g)
    case T.OpCancel{}:
      (at_reach.ca_good(t, k, g), (at_reach.ca_compat(t, k, g), at_reach.ca_size(t)))
    case T.OpRedo{side, x}:
      at_reach.local_redo(side, t, x, k, g)

# Edit, step, run
# ---------------

def at_reach.wrap_l_post(+sr: T.Step, +st: T.Status, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +q: Nat, +e: Nat, +g: at_reach.Good(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q), +ps: at_reach.Post(sr, l, q, e)) -> at_reach.Post(T.wrap_l(T.Info{st, s, lim, sp, dl, p}, own, sr, r), T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q, e):
  match sr:
    case T.Took{n}:
      at_reach.repl_l(st, s, lim, sp, dl, p, own, l, n, r, q, e, g, at_reach.p_good(n, l, q, e, ps), at_reach.p_compat(n, l, q, e, ps), at_reach.p_size(n, l, q, e, ps))
    case T.Refused{why}:
      Unit{}

def at_reach.wrap_r_post(+sr: T.Step, +st: T.Status, +s: List<&2, Bool>, +lim: T.Lim, +sp: Nat, +dl: T.Lim, +p: List<&2, Maybe<&2, Nat>>, +own: List<&2, Bool>, +l: T.Node, +r: T.Node, +q: Nat, +e: Nat, +g: at_reach.Good(T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q), +ps: at_reach.Post(sr, r, q, e)) -> at_reach.Post(T.wrap_r(T.Info{st, s, lim, sp, dl, p}, own, l, sr), T.Split{T.Info{st, s, lim, sp, dl, p}, own, l, r}, 1n+q, e):
  match sr:
    case T.Took{n}:
      at_reach.repl_r(st, s, lim, sp, dl, p, own, l, n, r, q, e, g, at_reach.p_good(n, r, q, e, ps), at_reach.p_compat(n, r, q, e, ps), at_reach.p_size(n, r, q, e, ps))
    case T.Refused{why}:
      Unit{}

# an op at any path keeps Good, is Compat, and adds extra(op) nodes
def at_reach.edit_post(+pa: List<&2, T.Dir>, +t: T.Node, +op: T.Op, +k: Nat, +g: at_reach.Good(t, k)) -> at_reach.Post(T.edit(pa, t, op, k), t, k, at_reach.extra(op)):
  match pa:
    case Nil{}:
      at_reach.local_post(op, t, k, g)
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              Unit{}
            case T.Split{i, own, l, r}:
              match i:
                case T.Info{st, s, lim, sp, dl, p}:
                  match k:
                    case 0n:
                      match g:
                    case 1n+q:
                      at_reach.wrap_l_post(T.edit(rest, l, op, q), st, s, lim, sp, dl, p, own, l, r, q, at_reach.extra(op), g, at_reach.edit_post(rest, l, op, q, at_reach.kid_l(st, s, lim, sp, dl, p, own, l, r, q, g)))
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              Unit{}
            case T.Split{i, own, l, r}:
              match i:
                case T.Info{st, s, lim, sp, dl, p}:
                  match k:
                    case 0n:
                      match g:
                    case 1n+q:
                      at_reach.wrap_r_post(T.edit(rest, r, op, q), st, s, lim, sp, dl, p, own, l, r, q, at_reach.extra(op), g, at_reach.edit_post(rest, r, op, q, at_reach.kid_r(st, s, lim, sp, dl, p, own, l, r, q, g)))

def at_reach.inv_good(+t: T.Node, +b: T.Bounds, -s: List<&2, Bool>, -lim: T.Lim, +iv: at_reach.Inv(t, b, s, lim)) -> at_reach.Good(t, T.bound_depth(b)):
  (g, iv1) = iv
  g

def at_reach.inv_scope(+t: T.Node, +b: T.Bounds, -s: List<&2, Bool>, -lim: T.Lim, +iv: at_reach.Inv(t, b, s, lim)) -> {T.scope_of(T.info(t)) == s : List<&2, Bool>}:
  (g, iv1) = iv
  (es, el) = iv1
  es

def at_reach.inv_lim(+t: T.Node, +b: T.Bounds, -s: List<&2, Bool>, -lim: T.Lim, +iv: at_reach.Inv(t, b, s, lim)) -> {T.limit_of(T.info(t)) == lim : T.Lim}:
  (g, iv1) = iv
  (es, el) = iv1
  el

def at_reach.after_inv(+sr: T.Step, +t: T.Node, +b: T.Bounds, -s: List<&2, Bool>, -lim: T.Lim, +e: Nat, +iv: at_reach.Inv(t, b, s, lim), +ps: at_reach.Post(sr, t, T.bound_depth(b), e)) -> at_reach.Inv(T.after(sr, t), b, s, lim):
  match sr:
    case T.Took{n}:
      (at_reach.p_good(n, t, T.bound_depth(b), e, ps), (Equal.trans(List<&2, Bool>, T.scope_of(T.info(n)), T.scope_of(T.info(t)), s, at_reach.c_scope(t, n, at_reach.p_compat(n, t, T.bound_depth(b), e, ps)), at_reach.inv_scope(t, b, s, lim, iv)), Equal.trans(T.Lim, T.limit_of(T.info(n)), T.limit_of(T.info(t)), lim, at_reach.c_lim(t, n, at_reach.p_compat(n, t, T.bound_depth(b), e, ps)), at_reach.inv_lim(t, b, s, lim, iv))))
    case T.Refused{why}:
      iv

# every event keeps the invariant
def at_reach.inv_step(+b: T.Bounds, +t: T.Node, +ev: T.Ev, -s: List<&2, Bool>, -lim: T.Lim, +iv: at_reach.Inv(t, b, s, lim)) -> at_reach.Inv(T.after(T.step(b, t, ev), t), b, s, lim):
  match ev:
    case T.EvSplit{at, own, ls, rs, hold}:
      at_reach.after_inv(T.edit(at, t, T.OpSplit{own, ls, rs, hold, Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), T.bound_margin(b)}, T.bound_depth(b)), t, b, s, lim, at_reach.extra(T.OpSplit{own, ls, rs, hold, Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), T.bound_margin(b)}), iv, at_reach.edit_post(at, t, T.OpSplit{own, ls, rs, hold, Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), T.bound_margin(b)}, T.bound_depth(b), at_reach.inv_good(t, b, s, lim, iv)))
    case T.EvSpend{at, n}:
      at_reach.after_inv(T.edit(at, t, T.OpSpend{n}, T.bound_depth(b)), t, b, s, lim, 0n, iv, at_reach.edit_post(at, t, T.OpSpend{n}, T.bound_depth(b), at_reach.inv_good(t, b, s, lim, iv)))
    case T.EvFinish{at, pq}:
      at_reach.after_inv(T.edit(at, t, T.OpFinish{pq}, T.bound_depth(b)), t, b, s, lim, 0n, iv, at_reach.edit_post(at, t, T.OpFinish{pq}, T.bound_depth(b), at_reach.inv_good(t, b, s, lim, iv)))
    case T.EvFail{at, pq}:
      at_reach.after_inv(T.edit(at, t, T.OpFail{pq}, T.bound_depth(b)), t, b, s, lim, 0n, iv, at_reach.edit_post(at, t, T.OpFail{pq}, T.bound_depth(b), at_reach.inv_good(t, b, s, lim, iv)))
    case T.EvCancel{at}:
      at_reach.after_inv(T.edit(at, t, T.OpCancel{}, T.bound_depth(b)), t, b, s, lim, 0n, iv, at_reach.edit_post(at, t, T.OpCancel{}, T.bound_depth(b), at_reach.inv_good(t, b, s, lim, iv)))
    case T.EvRedo{at, side, x}:
      at_reach.after_inv(T.edit(at, t, T.OpRedo{side, x}, T.bound_depth(b)), t, b, s, lim, 0n, iv, at_reach.edit_post(at, t, T.OpRedo{side, x}, T.bound_depth(b), at_reach.inv_good(t, b, s, lim, iv)))
    case T.EvTick{now}:
      at_reach.after_inv(T.Took{T.tick(t, now, False{})}, t, b, s, lim, 0n, iv, at_reach.tick_lem(t, now, False{}, T.bound_depth(b), at_reach.inv_good(t, b, s, lim, iv)))

def at_reach.after_size(+sr: T.Step, +t: T.Node, +e: Nat, +mx: Nat, +k: Nat, +h: {Nat.is_le(T.size(t), mx) == True{} : Bool}, +he: {Nat.is_le(Nat.add(e, T.size(t)), mx) == True{} : Bool}, +ps: at_reach.Post(sr, t, k, e)) -> {Nat.is_le(T.size(T.after(sr, t)), mx) == True{} : Bool}:
  match sr:
    case T.Took{n}:
      at_reach.tr(Nat, Nat.add(e, T.size(t)), T.size(n), z => {Nat.is_le(z, mx) == True{} : Bool}, Equal.sym(Nat, T.size(n), Nat.add(e, T.size(t)), at_reach.p_size(n, t, k, e, ps)), he)
    case T.Refused{why}:
      h

# a split is admitted only with room for its two nodes
def at_reach.room_ok(room: Bool, +sz: Nat, +mx: Nat, e: {room == Nat.is_le(Nat.add(sz, 2n), mx) : Bool}, h: {Nat.is_le(sz, mx) == True{} : Bool}) -> {Nat.is_le(Nat.add(at_reach.xroom(room), sz), mx) == True{} : Bool}:
  match room:
    case True{}:
      at_reach.tr(Nat, Nat.add(sz, 2n), Nat.add(2n, sz), z => {Nat.is_le(z, mx) == True{} : Bool}, at_reach.add_comm(sz, 2n), Equal.sym(Bool, True{}, Nat.is_le(Nat.add(sz, 2n), mx), e))
    case False{}:
      h

# every event keeps the node count within max_nodes
def at_reach.size_step(+b: T.Bounds, +t: T.Node, +ev: T.Ev, +g: at_reach.Good(t, T.bound_depth(b)), +h: {Nat.is_le(T.size(t), T.bound_nodes(b)) == True{} : Bool}) -> {Nat.is_le(T.size(T.after(T.step(b, t, ev), t)), T.bound_nodes(b)) == True{} : Bool}:
  match ev:
    case T.EvSplit{at, own, ls, rs, hold}:
      at_reach.after_size(T.edit(at, t, T.OpSplit{own, ls, rs, hold, Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), T.bound_margin(b)}, T.bound_depth(b)), t, at_reach.xroom(Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b))), T.bound_nodes(b), T.bound_depth(b), h, at_reach.room_ok(Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), T.size(t), T.bound_nodes(b), {==}, h), at_reach.edit_post(at, t, T.OpSplit{own, ls, rs, hold, Nat.is_le(Nat.add(T.size(t), 2n), T.bound_nodes(b)), T.bound_margin(b)}, T.bound_depth(b), g))
    case T.EvSpend{at, n}:
      at_reach.after_size(T.edit(at, t, T.OpSpend{n}, T.bound_depth(b)), t, 0n, T.bound_nodes(b), T.bound_depth(b), h, h, at_reach.edit_post(at, t, T.OpSpend{n}, T.bound_depth(b), g))
    case T.EvFinish{at, pq}:
      at_reach.after_size(T.edit(at, t, T.OpFinish{pq}, T.bound_depth(b)), t, 0n, T.bound_nodes(b), T.bound_depth(b), h, h, at_reach.edit_post(at, t, T.OpFinish{pq}, T.bound_depth(b), g))
    case T.EvFail{at, pq}:
      at_reach.after_size(T.edit(at, t, T.OpFail{pq}, T.bound_depth(b)), t, 0n, T.bound_nodes(b), T.bound_depth(b), h, h, at_reach.edit_post(at, t, T.OpFail{pq}, T.bound_depth(b), g))
    case T.EvCancel{at}:
      at_reach.after_size(T.edit(at, t, T.OpCancel{}, T.bound_depth(b)), t, 0n, T.bound_nodes(b), T.bound_depth(b), h, h, at_reach.edit_post(at, t, T.OpCancel{}, T.bound_depth(b), g))
    case T.EvRedo{at, side, x}:
      at_reach.after_size(T.edit(at, t, T.OpRedo{side, x}, T.bound_depth(b)), t, 0n, T.bound_nodes(b), T.bound_depth(b), h, h, at_reach.edit_post(at, t, T.OpRedo{side, x}, T.bound_depth(b), g))
    case T.EvTick{now}:
      at_reach.after_size(T.Took{T.tick(t, now, False{})}, t, 0n, T.bound_nodes(b), T.bound_depth(b), h, h, at_reach.tick_lem(t, now, False{}, T.bound_depth(b), g))

def at_reach.run_inv(+evs: List<&2, T.Ev>, +b: T.Bounds, +t: T.Node, -s: List<&2, Bool>, -lim: T.Lim, +iv: at_reach.Inv(t, b, s, lim)) -> at_reach.Inv(T.run(evs, b, t), b, s, lim):
  match evs:
    case Nil{}:
      iv
    case Con{e, es}:
      at_reach.run_inv(es, b, T.after(T.step(b, t, e), t), s, lim, at_reach.inv_step(b, t, e, s, lim, iv))

def at_reach.run_size(+evs: List<&2, T.Ev>, +b: T.Bounds, +t: T.Node, -s: List<&2, Bool>, -lim: T.Lim, +iv: at_reach.Inv(t, b, s, lim), +h: {Nat.is_le(T.size(t), T.bound_nodes(b)) == True{} : Bool}) -> {Nat.is_le(T.size(T.run(evs, b, t)), T.bound_nodes(b)) == True{} : Bool}:
  match evs:
    case Nil{}:
      h
    case Con{e, es}:
      at_reach.run_size(es, b, T.after(T.step(b, t, e), t), s, lim, at_reach.inv_step(b, t, e, s, lim, iv), at_reach.size_step(b, t, e, at_reach.inv_good(t, b, s, lim, iv), h))

def at_reach.init_inv(+b: T.Bounds, +s: List<&2, Bool>, +lim: T.Lim, +dl: T.Lim) -> at_reach.Inv(T.init(s, lim, dl), b, s, lim):
  (at_reach.has0(lim), ({==}, {==}))

# every reachable tree keeps the invariant
def at_reach.reach(+evs: List<&2, T.Ev>, +b: T.Bounds, +s: List<&2, Bool>, +lim: T.Lim, +dl: T.Lim) -> at_reach.Inv(T.run(evs, b, T.init(s, lim, dl)), b, s, lim):
  at_reach.run_inv(evs, b, T.init(s, lim, dl), s, lim, at_reach.init_inv(b, s, lim, dl))

# The laws
# --------

def at_reach.tiles_root(+evs: List<&2, T.Ev>, +b: T.Bounds, +s: List<&2, Bool>, +lim: T.Lim, +dl: T.Lim) -> {S.tile(T.run(evs, b, T.init(s, lim, dl))) == S.counts(s) : List<&2, Nat>}:
  +iv = at_reach.reach(evs, b, s, lim, dl)
  at_reach.tr(List<&2, Bool>, T.scope_of(T.info(T.run(evs, b, T.init(s, lim, dl)))), s, z => {S.tile(T.run(evs, b, T.init(s, lim, dl))) == S.counts(z) : List<&2, Nat>}, at_reach.inv_scope(T.run(evs, b, T.init(s, lim, dl)), b, s, lim, iv), at_reach.tile_of(T.run(evs, b, T.init(s, lim, dl)), T.bound_depth(b), at_reach.inv_good(T.run(evs, b, T.init(s, lim, dl)), b, s, lim, iv)))

def at_reach.no_orphan(+evs: List<&2, T.Ev>, +b: T.Bounds, +s: List<&2, Bool>, +lim: T.Lim, +dl: T.Lim) -> {S.no_orphan(T.run(evs, b, T.init(s, lim, dl))) == True{} : Bool}:
  at_reach.no_orphan_of(T.run(evs, b, T.init(s, lim, dl)), T.bound_depth(b), at_reach.inv_good(T.run(evs, b, T.init(s, lim, dl)), b, s, lim, at_reach.reach(evs, b, s, lim, dl)))

def at_reach.done_settled(+evs: List<&2, T.Ev>, +b: T.Bounds, +s: List<&2, Bool>, +lim: T.Lim, +dl: T.Lim) -> {S.done_settled(T.run(evs, b, T.init(s, lim, dl))) == True{} : Bool}:
  at_reach.done_of(T.run(evs, b, T.init(s, lim, dl)), T.bound_depth(b), at_reach.inv_good(T.run(evs, b, T.init(s, lim, dl)), b, s, lim, at_reach.reach(evs, b, s, lim, dl)))

def at_reach.budget_holds(+evs: List<&2, T.Ev>, +b: T.Bounds, +s: List<&2, Bool>, +lim: T.Lim, +dl: T.Lim) -> {S.has(S.spent_all(T.run(evs, b, T.init(s, lim, dl))), lim) == True{} : Bool}:
  +iv = at_reach.reach(evs, b, s, lim, dl)
  at_reach.tr(T.Lim, T.limit_of(T.info(T.run(evs, b, T.init(s, lim, dl)))), lim, z => {S.has(S.spent_all(T.run(evs, b, T.init(s, lim, dl))), z) == True{} : Bool}, at_reach.inv_lim(T.run(evs, b, T.init(s, lim, dl)), b, s, lim, iv), at_reach.fits_all(T.run(evs, b, T.init(s, lim, dl)), T.bound_depth(b), at_reach.inv_good(T.run(evs, b, T.init(s, lim, dl)), b, s, lim, iv)))

def at_reach.deadlines_down(+evs: List<&2, T.Ev>, +b: T.Bounds, +s: List<&2, Bool>, +lim: T.Lim, +dl: T.Lim) -> {S.deadlines_down(T.run(evs, b, T.init(s, lim, dl))) == True{} : Bool}:
  at_reach.dd_of(T.run(evs, b, T.init(s, lim, dl)), T.bound_depth(b), at_reach.inv_good(T.run(evs, b, T.init(s, lim, dl)), b, s, lim, at_reach.reach(evs, b, s, lim, dl)))

def at_reach.depth_bound(+evs: List<&2, T.Ev>, +b: T.Bounds, +s: List<&2, Bool>, +lim: T.Lim, +dl: T.Lim) -> {Nat.is_le(S.depth(T.run(evs, b, T.init(s, lim, dl))), T.bound_depth(b)) == True{} : Bool}:
  at_reach.depth_of(T.run(evs, b, T.init(s, lim, dl)), T.bound_depth(b), at_reach.inv_good(T.run(evs, b, T.init(s, lim, dl)), b, s, lim, at_reach.reach(evs, b, s, lim, dl)))

def at_reach.nodes_bound(+evs: List<&2, T.Ev>, +b: T.Bounds, +s: List<&2, Bool>, +lim: T.Lim, +dl: T.Lim, e: {Nat.is_le(1n, T.bound_nodes(b)) == True{} : Bool}) -> {Nat.is_le(S.nodes(T.run(evs, b, T.init(s, lim, dl))), T.bound_nodes(b)) == True{} : Bool}:
  at_reach.tr(Nat, T.size(T.run(evs, b, T.init(s, lim, dl))), S.nodes(T.run(evs, b, T.init(s, lim, dl))), z => {Nat.is_le(z, T.bound_nodes(b)) == True{} : Bool}, Equal.sym(Nat, S.nodes(T.run(evs, b, T.init(s, lim, dl))), T.size(T.run(evs, b, T.init(s, lim, dl))), at_reach.nodes_size(T.run(evs, b, T.init(s, lim, dl)))), at_reach.run_size(evs, b, T.init(s, lim, dl), s, lim, at_reach.init_inv(b, s, lim, dl), e))
