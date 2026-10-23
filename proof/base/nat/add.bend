# eukhe: lemmas the proofs of two or more areas share: nat/add

import Base
import ../../../bend/run.bend as Rn
import ../bool/misc.bend as LBoolMisc
import ./misc.bend as LNatMisc

# ---- Nat.add (copied from the skill's examples/sort/proof/nat_add.bend) ----

def wn_add_zero_r(m: Nat) -> {Nat.add(m, 0n) == m : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 0n), p, wn_add_zero_r(p))

def wn_add_succ_r(m: Nat, -n: Nat) -> {Nat.add(m, 1n+n) == 1n+Nat.add(m, n) : Nat}:
  match m:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, 1n+n), 1n+Nat.add(p, n), wn_add_succ_r(p, n))

def wn_add_comm(m: Nat, +n: Nat) -> {Nat.add(m, n) == Nat.add(n, m) : Nat}:
  match m:
    case 0n:
      Equal.sym(Nat, Nat.add(n, 0n), n, wn_add_zero_r(n))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(n, 1n+p), 1n+Nat.add(n, p), wn_add_succ_r(n, p)) : {1n+Nat.add(p, n) == _ : Nat}
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, n), Nat.add(n, p), wn_add_comm(p, n))

def wn_add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)),
        wn_add_assoc(p, b, c))

def wn_add_swap(+a: Nat, +b: Nat, +c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  Equal.trans(Nat, Nat.add(a, Nat.add(b, c)), Nat.add(Nat.add(a, b), c), Nat.add(b, Nat.add(a, c)),
    Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), wn_add_assoc(a, b, c)),
    Equal.trans(Nat, Nat.add(Nat.add(a, b), c), Nat.add(Nat.add(b, a), c), Nat.add(b, Nat.add(a, c)),
      Equal.cong(Nat, Nat, k => Nat.add(k, c), Nat.add(a, b), Nat.add(b, a), wn_add_comm(a, b)),
      wn_add_assoc(b, a, c)))

def wn_mul_succ_r(+a: Nat, +w: Nat) -> {Nat.mul(a, 1n+w) == Nat.add(a, Nat.mul(a, w)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(p, 1n+w), Nat.add(p, Nat.mul(p, w)), wn_mul_succ_r(p, w)) : {1n+Nat.add(w, _) == 1n+Nat.add(p, Nat.add(w, Nat.mul(p, w))) : Nat}
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(w, Nat.add(p, Nat.mul(p, w))), Nat.add(p, Nat.add(w, Nat.mul(p, w))),
        wn_add_swap(w, p, Nat.mul(p, w)))

def wn_le_k(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.add(a, LNatMisc.wn_sub(b, a)) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LBoolMisc.wn_absurd({Nat.add(1n+p, 0n) == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, LNatMisc.wn_sub(q, p)), q, wn_le_k(p, q, h))

def pa.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      LNatMisc.pa.succ(Nat.add(p, 0n), p, pa.add_zero(p))

def pa.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      LNatMisc.pa.succ(Nat.add(p, 1n+b), 1n+Nat.add(p, b), pa.add_succ(p, b))

def pa.add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, pa.add_zero(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p), LNatMisc.pa.succ(Nat.add(p, b), Nat.add(b, p), pa.add_comm(p, b)), Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), pa.add_succ(b, p)))

# Numbers
# -------

def add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %add_assoc(p, b, c) : {1n+Nat.add(Nat.add(p, b), c) == 1n+_ : Nat}
      {==}

def add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      %add_comm(p, b) : {1n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# a + (b + c) = b + (a + c)
def add_lcomm(+a: Nat, +b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  %add_assoc(a, b, c) : {_ == Nat.add(b, Nat.add(a, c)) : Nat}
  %Equal.sym(Nat, Nat.add(a, b), Nat.add(b, a), add_comm(a, b)) : {Nat.add(_, c) == Nat.add(b, Nat.add(a, c)) : Nat}
  add_assoc(b, a, c)

def add_succ_r(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  Equal.sym(Nat, Nat.add(a, 1n+b), 1n+Nat.add(a, b), add_succ(a, b))

def add_assoc_r(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(Nat.add(a, b), c) : Nat}:
  Equal.sym(Nat, Nat.add(Nat.add(a, b), c), Nat.add(a, Nat.add(b, c)), add_assoc(a, b, c))

# a fall within the generation is a fall of M
def lift(k: Nat, -gs: Nat, -gt: Nat, -X: Nat, e: {gs == Nat.add(k, 1n+gt) : Nat}) -> {Nat.add(gs, 1n+X) == Nat.add(k, 1n+Nat.add(gt, 1n+X)) : Nat}:
  %Equal.sym(Nat, gs, Nat.add(k, 1n+gt), e) : {Nat.add(_, 1n+X) == Nat.add(k, 1n+Nat.add(gt, 1n+X)) : Nat}
  add_assoc(k, 1n+gt, 1n+X)

# a run that ends takes no more inputs
def to_end(+gs: Nat, +X: Nat) -> {Nat.add(gs, 1n+X) == Nat.add(Nat.add(gs, X), 1n+0n) : Nat}:
  %add_succ_r(Nat.add(gs, X), 0n) : {Nat.add(gs, 1n+X) == _ : Nat}
  %Equal.sym(Nat, Nat.add(Nat.add(gs, X), 0n), Nat.add(gs, X), add_zero(Nat.add(gs, X))) : {Nat.add(gs, 1n+X) == 1n+_ : Nat}
  add_succ(gs, X)

# call -> tools: the generation's round starts
def call_tools(+X: Nat) -> {1n+X == Nat.add(X, 1n+0n) : Nat}:
  %add_succ_r(X, 0n) : {1n+X == _ : Nat}
  %add_zero(X) : {1n+_ == 1n+Nat.add(X, 0n) : Nat}
  {==}

# tools -> prepare: the next generation
def next_gen(+gp: Nat, +X: Nat) -> {Nat.add(0n, 1n+Nat.add(1n+gp, X)) == Nat.add(0n, 1n+Nat.add(gp, 1n+X)) : Nat}:
  %add_succ(gp, X) : {1n+_ == 1n+Nat.add(gp, 1n+X) : Nat}
  {==}

def call_end(+P: Nat, +U: Nat, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> {Nat.add(LNatMisc.gen(P, Rn.Call{}, c, u, p), 1n+LNatMisc.X(P, U, r)) == Nat.add(LNatMisc.K.call_end(P, U, r, c, u, p), 1n+0n) : Nat}:
  to_end(LNatMisc.gen(P, Rn.Call{}, c, u, p), LNatMisc.X(P, U, r))

def succ_m(+j: Nat, +g: Nat, +X: Nat) -> {Nat.add(j, Nat.add(g, 1n+X)) == 1n+Nat.add(j, Nat.add(g, X)) : Nat}:
  %add_succ_r(g, X) : {Nat.add(j, _) == 1n+Nat.add(j, Nat.add(g, X)) : Nat}
  add_succ(j, Nat.add(g, X))

# a live run may still take an input
def pos(-T: Type, +j: Nat, +g: Nat, +X: Nat, h: {0n == Nat.add(j, Nat.add(g, 1n+X)) : Nat}) -> T:
  LNatMisc.zero_succ(T, Nat.add(j, Nat.add(g, X)), Equal.trans(Nat, 0n, Nat.add(j, Nat.add(g, 1n+X)), 1n+Nat.add(j, Nat.add(g, X)), h, succ_m(j, g, X)))

def next_len1(-n: Nat, +j: Nat, +k: Nat, -ms: Nat, -mt: Nat, h: {1n+n == Nat.add(j, ms) : Nat}, eq: {ms == Nat.add(k, 1n+mt) : Nat}) -> {1n+n == 1n+Nat.add(Nat.add(j, k), mt) : Nat}:
  %add_succ(Nat.add(j, k), mt) : {1n+n == _ : Nat}
  %add_assoc_r(j, k, 1n+mt) : {1n+n == _ : Nat}
  %eq : {1n+n == Nat.add(j, _) : Nat}
  h

# a + b == 0: both are 0
def auth_flight.pf.add_zero(a: Nat, -b: Nat, e: {Nat.add(a, b) == 0n : Nat}) -> ({a == 0n : Nat} & {b == 0n : Nat}):
  match a:
    case 0n:
      ({==}, e)
    case 1n+p:
      LNatMisc.pf.succ_ne_zero(({1n+p == 0n : Nat} & {b == 0n : Nat}), Nat.add(p, b), e)

def rk.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %rk.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

# b + (a + c) == a + (b + c)
def rk.add_swap(a: Nat, +b: Nat, -c: Nat) -> {Nat.add(b, Nat.add(a, c)) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %rk.add_swap(p, b, c) : {Nat.add(b, 1n+Nat.add(p, c)) == 1n+_ : Nat}
      rk.add_succ(b, Nat.add(p, c))

# n + (x - n) = x when n <= x
def pu.sub_add(+n: Nat, +x: Nat, +e: {Nat.is_le(n, x) == True{} : Bool}) -> {Nat.add(n, Nat.sub(x, n)) == x : Nat}:
  match n x:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LBoolMisc.pu.absurd_ft({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, e)
    case 1n+p 1n+q:
      %pu.sub_add(p, q, e) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}
