# eukhe: lemmas of LAW goal_text_left_value: Nat arithmetic
#
# The sums and products of the value arguments (lv.*), each by induction
# on the argument Nat.add / Nat.mul recurse on; inequalities as
# {Nat.is_le(a, b) == True{} : Bool}, a < b as Nat.is_le(1n+a, b).

import Base

def lv.When(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# False is not True
def lv.absurd(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : lv.When(_, G)
  Unit{}

def lv.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, lv.add_zero(p))

def lv.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), lv.add_succ(p, b))

def lv.add_comm(a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, lv.add_zero(b))
    case 1n+p:
      %Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), lv.add_succ(b, p)) : {1n+Nat.add(p, b) == _ : Nat}
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, b), Nat.add(b, p), lv.add_comm(p, b))

def lv.add_assoc(a: Nat, -b: Nat, -c: Nat) -> {Nat.add(Nat.add(a, b), c) == Nat.add(a, Nat.add(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(Nat.add(p, b), c), Nat.add(p, Nat.add(b, c)), lv.add_assoc(p, b, c))

# a + (b + c) == b + (a + c)
def lv.add_swap(+a: Nat, +b: Nat, -c: Nat) -> {Nat.add(a, Nat.add(b, c)) == Nat.add(b, Nat.add(a, c)) : Nat}:
  %lv.add_assoc(a, b, c) : {_ == Nat.add(b, Nat.add(a, c)) : Nat}
  %lv.add_assoc(b, a, c) : {Nat.add(Nat.add(a, b), c) == _ : Nat}
  Equal.cong(Nat, Nat, z => Nat.add(z, c), Nat.add(a, b), Nat.add(b, a), lv.add_comm(a, b))

def lv.mul_zero(n: Nat) -> {Nat.mul(n, 0n) == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lv.mul_zero(p)

def lv.mul_succ(a: Nat, +w: Nat) -> {Nat.mul(a, 1n+w) == Nat.add(a, Nat.mul(a, w)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(p, 1n+w), Nat.add(p, Nat.mul(p, w)), lv.mul_succ(p, w)) : {1n+Nat.add(w, _) == Nat.add(1n+p, Nat.mul(1n+p, w)) : Nat}
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(w, Nat.add(p, Nat.mul(p, w))), Nat.add(p, Nat.add(w, Nat.mul(p, w))), lv.add_swap(w, p, Nat.mul(p, w)))

def lv.mul_comm(a: Nat, +b: Nat) -> {Nat.mul(a, b) == Nat.mul(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.mul(b, 0n), 0n, lv.mul_zero(b))
    case 1n++p:
      %Equal.sym(Nat, Nat.mul(b, 1n+p), Nat.add(b, Nat.mul(b, p)), lv.mul_succ(b, p)) : {Nat.add(b, Nat.mul(p, b)) == _ : Nat}
      Equal.cong(Nat, Nat, z => Nat.add(b, z), Nat.mul(p, b), Nat.mul(b, p), lv.mul_comm(p, b))

def lv.mul_one(n: Nat) -> {Nat.mul(n, 1n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.mul(p, 1n), p, lv.mul_one(p))

# (a + b) * c == a * c + b * c
def lv.mul_dist_r(a: Nat, -b: Nat, +c: Nat) -> {Nat.mul(Nat.add(a, b), c) == Nat.add(Nat.mul(a, c), Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.mul(Nat.add(p, b), c), Nat.add(Nat.mul(p, c), Nat.mul(b, c)), lv.mul_dist_r(p, b, c)) : {Nat.add(c, _) == Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(c, Nat.mul(p, c)), Nat.mul(b, c)), Nat.add(c, Nat.add(Nat.mul(p, c), Nat.mul(b, c))), lv.add_assoc(c, Nat.mul(p, c), Nat.mul(b, c)))

# a * (b + c) == a * b + a * c
def lv.mul_dist_l(+a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(a, b), Nat.mul(a, c)) : Nat}:
  %lv.mul_comm(b, a) : {Nat.mul(a, Nat.add(b, c)) == Nat.add(_, Nat.mul(a, c)) : Nat}
  %lv.mul_comm(c, a) : {Nat.mul(a, Nat.add(b, c)) == Nat.add(Nat.mul(b, a), _) : Nat}
  %lv.mul_comm(Nat.add(b, c), a) : {_ == Nat.add(Nat.mul(b, a), Nat.mul(c, a)) : Nat}
  lv.mul_dist_r(b, c, a)

def lv.mul_assoc(a: Nat, +b: Nat, +c: Nat) -> {Nat.mul(Nat.mul(a, b), c) == Nat.mul(a, Nat.mul(b, c)) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %lv.mul_assoc(p, b, c) : {Nat.mul(Nat.add(b, Nat.mul(p, b)), c) == Nat.add(Nat.mul(b, c), _) : Nat}
      lv.mul_dist_r(b, Nat.mul(p, b), c)

# Inequalities
# ------------

def lv.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def lv.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lv.le_refl(p)

def lv.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      lv.le_zero(c)
    case 1n+x 0n c:
      lv.absurd({Nat.is_le(1n+x, c) == True{} : Bool}, ab)
    case 1n+x 1n+y 0n:
      lv.absurd({Nat.is_le(1n+x, 0n) == True{} : Bool}, bc)
    case 1n+x 1n+y 1n+z:
      lv.le_trans(x, y, z, ab, bc)

# a <= a + b
def lv.le_add(a: Nat, b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      lv.le_zero(b)
    case 1n+p:
      lv.le_add(p, b)

# b <= a + b
def lv.le_add_l(+a: Nat, +b: Nat) -> {Nat.is_le(b, Nat.add(a, b)) == True{} : Bool}:
  %lv.add_comm(b, a) : {Nat.is_le(b, _) == True{} : Bool}
  lv.le_add(b, a)

# k + a <= k + b when a <= b
def lv.add_le_l(k: Nat, -a: Nat, -b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(k, a), Nat.add(k, b)) == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n+p:
      lv.add_le_l(p, a, b, h)

# a + k <= b + k when a <= b
def lv.add_le_r(+a: Nat, +b: Nat, +k: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, k), Nat.add(b, k)) == True{} : Bool}:
  %lv.add_comm(k, a) : {Nat.is_le(_, Nat.add(b, k)) == True{} : Bool}
  %lv.add_comm(k, b) : {Nat.is_le(Nat.add(k, a), _) == True{} : Bool}
  lv.add_le_l(k, a, b, h)

# a + c <= b + d when a <= b and c <= d
def lv.add_le(+a: Nat, +b: Nat, +c: Nat, +d: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, cd: {Nat.is_le(c, d) == True{} : Bool}) -> {Nat.is_le(Nat.add(a, c), Nat.add(b, d)) == True{} : Bool}:
  lv.le_trans(Nat.add(a, c), Nat.add(b, c), Nat.add(b, d), lv.add_le_r(a, b, c, ab), lv.add_le_l(b, c, d, cd))

# a * c <= b * c when a <= b
def lv.mul_le_l(a: Nat, b: Nat, +c: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.mul(a, c), Nat.mul(b, c)) == True{} : Bool}:
  match a b:
    case 0n b:
      lv.le_zero(Nat.mul(b, c))
    case 1n+x 0n:
      lv.absurd({Nat.is_le(Nat.mul(1n+x, c), Nat.mul(0n, c)) == True{} : Bool}, h)
    case 1n+x 1n+y:
      lv.add_le_l(c, Nat.mul(x, c), Nat.mul(y, c), lv.mul_le_l(x, y, c, h))

# k * a <= k * b when a <= b
def lv.mul_le_r(+k: Nat, +a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(Nat.mul(k, a), Nat.mul(k, b)) == True{} : Bool}:
  %lv.mul_comm(a, k) : {Nat.is_le(_, Nat.mul(k, b)) == True{} : Bool}
  %lv.mul_comm(b, k) : {Nat.is_le(Nat.mul(a, k), _) == True{} : Bool}
  lv.mul_le_l(a, b, k, h)

# 1 + a <= a never holds
def lv.succ_le_self(a: Nat) -> {Nat.is_le(1n+a, a) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      lv.succ_le_self(p)

# Subtraction
# -----------

def lv.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# (a + b) - b == a
def lv.sub_add(+a: Nat, b: Nat) -> {Nat.sub(Nat.add(a, b), b) == a : Nat}:
  match b:
    case 0n:
      %Equal.sym(Nat, Nat.add(a, 0n), a, lv.add_zero(a)) : {Nat.sub(_, 0n) == a : Nat}
      lv.sub_zero(a)
    case 1n+q:
      %Equal.sym(Nat, Nat.add(a, 1n+q), 1n+Nat.add(a, q), lv.add_succ(a, q)) : {Nat.sub(_, 1n+q) == a : Nat}
      lv.sub_add(a, q)

# c - b == a when a + b == c
def lv.sub_of(+a: Nat, +b: Nat, -c: Nat, e: {Nat.add(a, b) == c : Nat}) -> {Nat.sub(c, b) == a : Nat}:
  %e : {Nat.sub(_, b) == a : Nat}
  lv.sub_add(a, b)

# a - b == 0 when a <= b
def lv.sub_le(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n b:
      {==}
    case 1n+x 0n:
      lv.absurd({Nat.sub(1n+x, 0n) == 0n : Nat}, h)
    case 1n+x 1n+y:
      lv.sub_le(x, y, h)
