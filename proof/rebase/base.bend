# eukhe: lemmas of the proofs of area rebase: logic, Nat order, the
# lists the rule cuts (take, drop, append, length), and facts of the spec
# (spec/harness/rebase.bend) the laws share

import Base
import ../../bend/rebase.bend as R
import ../../spec/harness/rebase.bend as RbSpec

# Logic
# -----

def rb.If(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

# True is not False
def rb.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : rb.If(_, Unit, A)
  Unit{}

def rb.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  rb.absurd(A, Equal.sym(Bool, False{}, True{}, e))

def rb.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      rb.absurdF({False{} == True{} : Bool}, e)

def rb.and_r(a: Bool, b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      rb.absurdF({b == True{} : Bool}, e)

def rb.and_t(-a: Bool, -b: Bool, ea: {a == True{} : Bool}, eb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  %Equal.sym(Bool, a, True{}, ea) : {Bool.and(_, b) == True{} : Bool}
  %Equal.sym(Bool, b, True{}, eb) : {Bool.and(True{}, _) == True{} : Bool}
  {==}

def rb.and_true_r(a: Bool) -> {Bool.and(a, True{}) == a : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def rb.and_false_r(a: Bool) -> {Bool.and(a, False{}) == False{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def rb.and_comm(a: Bool, b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

# Nat order
# ---------

def rb.eq_true(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      rb.absurdF({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      rb.absurdF({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, rb.eq_true(p, q, e))

def rb.eq_refl(a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      rb.eq_refl(p)

def rb.le_zero(a: Nat) -> {Nat.is_le(0n, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def rb.le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      rb.le_refl(p)

# 1 + a <= b is a < b
def rb.le_succ(a: Nat, b: Nat) -> {Nat.is_le(1n+a, b) == Nat.is_lt(a, b) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      rb.le_zero(q)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rb.le_succ(p, q)

def rb.lt_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      rb.absurdF({Nat.is_le(0n, 0n) == True{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      rb.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      rb.lt_le(p, q, e)

# a < b <= c: a < c
def rb.lt_le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_lt(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n _:
      rb.absurdF({Nat.is_lt(0n, c) == True{} : Bool}, ab)
    case 0n 1n+q 0n:
      rb.absurdF({Nat.is_lt(0n, 0n) == True{} : Bool}, bc)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      rb.absurdF({Nat.is_lt(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      rb.absurdF({Nat.is_lt(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      rb.lt_le_trans(p, q, r, ab, bc)

# a <= b and a != b: a < b
def rb.le_ne_lt(a: Nat, b: Nat, le: {Nat.is_le(a, b) == True{} : Bool}, ne: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_lt(a, b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      rb.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ne)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      rb.absurdF({Nat.is_lt(1n+p, 0n) == True{} : Bool}, le)
    case 1n+p 1n+q:
      rb.le_ne_lt(p, q, le, ne)

# a < b: a is not b
def rb.lt_ne(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      rb.absurdF({Nat.is_eq(0n, 0n) == False{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rb.lt_ne(p, q, e)

# b <= a: a < b is false
def rb.le_not_lt(a: Nat, b: Nat, e: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.is_lt(a, b) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      rb.absurdF({Nat.is_lt(0n, 1n+q) == False{} : Bool}, e)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rb.le_not_lt(p, q, e)

def rb.le_add(a: Nat, b: Nat) -> {Nat.is_le(a, Nat.add(a, b)) == True{} : Bool}:
  match a:
    case 0n:
      rb.le_zero(b)
    case 1n+p:
      rb.le_add(p, b)

def rb.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(p, 0n), p, rb.add_zero(p))

def rb.sub_zero(a: Nat) -> {Nat.sub(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

def rb.sub_self(a: Nat) -> {Nat.sub(a, a) == 0n : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      rb.sub_self(p)

# (a + b) - a is b
def rb.add_sub(a: Nat, +b: Nat) -> {Nat.sub(Nat.add(a, b), a) == b : Nat}:
  match a:
    case 0n:
      rb.sub_zero(b)
    case 1n+p:
      rb.add_sub(p, b)

# Lists
# -----

def rb.take_zero(xs: List<&2, Nat>) -> {List.take(&2, Nat, xs, 0n) == Nil{} : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

def rb.app_nil(xs: List<&2, Nat>) -> {List.append(&2, Nat, xs, Nil{}) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, t}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, r => x <> r, List.append(&2, Nat, t, Nil{}), t, rb.app_nil(t))

def rb.lt_zero(a: Nat) -> {Nat.is_lt(a, 0n) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      {==}

# The spec
# --------

# valid edits have no first bad edit
def rb.none_true(m: Maybe<&2, Nat>, e: {RbSpec.none(m) == True{} : Bool}) -> {m == None{} : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{i}:
      rb.absurdF({Some{i} == None{} : Maybe<&2, Nat>}, e)

def rb.same_refl(a: List<&2, Nat>) -> {RbSpec.same(a, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, xs}:
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, rb.eq_refl(x)) : {Bool.and(_, RbSpec.same(xs, xs)) == True{} : Bool}
      rb.same_refl(xs)

def rb.LC(l: List<&2, Nat>, G: Type) -> Type:
  match l:
    case Nil{}:
      Unit
    case Con{x, r}:
      G

# Nil is not a cons
def rb.nil_con(-A: Type, -j: Nat, -l: List<&2, Nat>, e: {Nil{} == j <> l : List<&2, Nat>}) -> A:
  %e : rb.LC(_, A)
  Unit{}

def rb.NZ(n: Nat, G: Type) -> Type:
  match n:
    case 0n:
      Unit
    case 1n+p:
      G

# 0 is not a successor
def rb.zero_succ(-A: Type, -q: Nat, e: {0n == 1n+q : Nat}) -> A:
  %e : rb.NZ(_, A)
  Unit{}

def rb.hd(l: List<&2, Nat>) -> Nat:
  match l:
    case Nil{}:
      0n
    case Con{x, r}:
      x

def rb.le_of_succ(a: Nat, b: Nat, e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case 0n _:
      rb.le_zero(b)
    case 1n+p 0n:
      rb.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      rb.le_of_succ(p, q, e)

# b - a is one more than b - (1 + a) when a < b
def rb.sub_succ(a: Nat, b: Nat, e: {Nat.is_le(1n+a, b) == True{} : Bool}) -> {Nat.sub(b, a) == 1n+Nat.sub(b, 1n+a) : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          rb.absurdF({Nat.sub(0n, 0n) == 1n+Nat.sub(0n, 1n) : Nat}, e)
        case 1n+q:
          Equal.cong(Nat, Nat, n => 1n+n, q, Nat.sub(q, 0n), Equal.sym(Nat, Nat.sub(q, 0n), q, rb.sub_zero(q)))
    case 1n+p:
      match b:
        case 0n:
          rb.absurdF({Nat.sub(0n, 1n+p) == 1n+Nat.sub(0n, 2n+p) : Nat}, e)
        case 1n+q:
          rb.sub_succ(p, q, e)

def rb.sub_le(t: Nat, n: Nat, s: Nat, e: {Nat.is_le(t, n) == True{} : Bool}) -> {Nat.is_le(Nat.sub(t, s), Nat.sub(n, s)) == True{} : Bool}:
  match t:
    case 0n:
      rb.le_zero(Nat.sub(n, s))
    case 1n+p:
      match n:
        case 0n:
          rb.absurdF({Nat.is_le(Nat.sub(1n+p, s), Nat.sub(0n, s)) == True{} : Bool}, e)
        case 1n+m:
          match s:
            case 0n:
              e
            case 1n+r:
              rb.sub_le(p, m, r, e)

def rb.drop_zero(y: List<&2, Nat>) -> {List.drop(&2, Nat, y, 0n) == y : List<&2, Nat>}:
  match y:
    case Nil{}:
      {==}
    case Con{x, r}:
      {==}

def rb.drop_drop(j: Nat, h: List<&2, Nat>, +m: Nat) -> {List.drop(&2, Nat, List.drop(&2, Nat, h, j), m) == List.drop(&2, Nat, h, Nat.add(j, m)) : List<&2, Nat>}:
  match j:
    case 0n:
      %Equal.sym(List<&2, Nat>, List.drop(&2, Nat, h, 0n), h, rb.drop_zero(h)) : {List.drop(&2, Nat, _, m) == List.drop(&2, Nat, h, m) : List<&2, Nat>}
      {==}
    case 1n+q:
      match h:
        case Nil{}:
          {==}
        case Con{x, r}:
          rb.drop_drop(q, r, m)

def rb.len_drop(b: List<&2, Nat>, s: Nat) -> {List.length(&2, Nat, List.drop(&2, Nat, b, s)) == Nat.sub(List.length(&2, Nat, b), s) : Nat}:
  match b:
    case Nil{}:
      {==}
    case Con{x, r}:
      match s:
        case 0n:
          {==}
        case 1n+q:
          rb.len_drop(r, q)

def rb.len_take(y: List<&2, Nat>, n: Nat, e: {Nat.is_le(n, List.length(&2, Nat, y)) == True{} : Bool}) -> {List.length(&2, Nat, List.take(&2, Nat, y, n)) == n : Nat}:
  match y:
    case Nil{}:
      match n:
        case 0n:
          {==}
        case 1n+q:
          rb.absurdF({0n == 1n+q : Nat}, e)
    case Con{x, r}:
      match n:
        case 0n:
          {==}
        case 1n+q:
          Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Nat, List.take(&2, Nat, r, q)), q, rb.len_take(r, q, e))

# the lines [s, t) of b within b are t - s lines
def rb.len_region(+b: List<&2, Nat>, +s: Nat, +t: Nat, inside: {Nat.is_le(t, List.length(&2, Nat, b)) == True{} : Bool}) -> {List.length(&2, Nat, List.take(&2, Nat, List.drop(&2, Nat, b, s), Nat.sub(t, s))) == Nat.sub(t, s) : Nat}:
  +le = rb.sub_le(t, List.length(&2, Nat, b), s, inside)
  +d = List.drop(&2, Nat, b, s)
  rb.len_take(d, Nat.sub(t, s), Equal.trans(Bool, Nat.is_le(Nat.sub(t, s), List.length(&2, Nat, d)), Nat.is_le(Nat.sub(t, s), Nat.sub(List.length(&2, Nat, b), s)), True{}, Equal.cong(Nat, Bool, z => Nat.is_le(Nat.sub(t, s), z), List.length(&2, Nat, d), Nat.sub(List.length(&2, Nat, b), s), rb.len_drop(b, s)), le))

# Prefixes
# --------

def rb.st.app(a: List<&2, Nat>, +c: List<&2, Nat>, y: List<&2, Nat>, e: {RbSpec.starts(List.append(&2, Nat, a, c), y) == True{} : Bool}) -> {RbSpec.starts(c, List.drop(&2, Nat, y, List.length(&2, Nat, a))) == True{} : Bool}:
  match a:
    case Nil{}:
      %Equal.sym(List<&2, Nat>, List.drop(&2, Nat, y, 0n), y, rb.drop_zero(y)) : {RbSpec.starts(c, _) == True{} : Bool}
      e
    case Con{+x, +at}:
      match y:
        case Nil{}:
          rb.absurdF({RbSpec.starts(c, Nil{}) == True{} : Bool}, e)
        case Con{+d, +yt}:
          rb.st.app(at, c, yt, rb.and_r(Nat.is_eq(x, d), RbSpec.starts(List.append(&2, Nat, at, c), yt), e))

def rb.st.take(rg: List<&2, Nat>, +rc: List<&2, Nat>, y: List<&2, Nat>, e: {RbSpec.starts(List.append(&2, Nat, rg, rc), y) == True{} : Bool}) -> {RbSpec.same(List.take(&2, Nat, y, List.length(&2, Nat, rg)), rg) == True{} : Bool}:
  match rg:
    case Nil{}:
      %Equal.sym(List<&2, Nat>, List.take(&2, Nat, y, 0n), Nil{}, rb.take_zero(y)) : {RbSpec.same(_, Nil{}) == True{} : Bool}
      {==}
    case Con{+x, +rt}:
      match y:
        case Nil{}:
          rb.absurdF({RbSpec.same(Nil{}, x <> rt) == True{} : Bool}, e)
        case Con{+d, +yt}:
          +e0 = e
          +ex = rb.eq_true(x, d, rb.and_l(Nat.is_eq(x, d), RbSpec.starts(List.append(&2, Nat, rt, rc), yt), e0))
          %ex : {Bool.and(Nat.is_eq(_, x), RbSpec.same(List.take(&2, Nat, yt, List.length(&2, Nat, rt)), rt)) == True{} : Bool}
          %Equal.sym(Bool, Nat.is_eq(x, x), True{}, rb.eq_refl(x)) : {Bool.and(_, RbSpec.same(List.take(&2, Nat, yt, List.length(&2, Nat, rt)), rt)) == True{} : Bool}
          rb.st.take(rt, rc, yt, rb.and_r(Nat.is_eq(x, d), RbSpec.starts(List.append(&2, Nat, rt, rc), yt), e0))

def rb.st.len(w: List<&2, Nat>, y: List<&2, Nat>, e: {RbSpec.starts(w, y) == True{} : Bool}) -> {Nat.is_le(List.length(&2, Nat, w), List.length(&2, Nat, y)) == True{} : Bool}:
  match w:
    case Nil{}:
      rb.le_zero(List.length(&2, Nat, y))
    case Con{+x, +wt}:
      match y:
        case Nil{}:
          rb.absurdF({Nat.is_le(List.length(&2, Nat, x <> wt), 0n) == True{} : Bool}, e)
        case Con{+d, +yt}:
          rb.st.len(wt, yt, rb.and_r(Nat.is_eq(x, d), RbSpec.starts(wt, yt), e))

# a nonempty window at j of h ends within h
def rb.st.bound(j: Nat, h: List<&2, Nat>, +x: Nat, +wt: List<&2, Nat>, e: {RbSpec.starts(x <> wt, List.drop(&2, Nat, h, j)) == True{} : Bool}) -> {Nat.is_le(Nat.add(j, 1n+List.length(&2, Nat, wt)), List.length(&2, Nat, h)) == True{} : Bool}:
  match j:
    case 0n:
      match h:
        case Nil{}:
          rb.absurdF({Nat.is_le(1n+List.length(&2, Nat, wt), 0n) == True{} : Bool}, e)
        case Con{+d, +ht}:
          rb.st.len(wt, ht, rb.and_r(Nat.is_eq(x, d), RbSpec.starts(wt, ht), e))
    case 1n+q:
      match h:
        case Nil{}:
          rb.absurdF({Nat.is_le(1n+Nat.add(q, 1n+List.length(&2, Nat, wt)), 0n) == True{} : Bool}, e)
        case Con{d, ht}:
          rb.st.bound(q, ht, x, wt, e)

# Copies
# ------

def rb.cp.nil(q: Bool, -w: List<&2, Nat>, eq: {RbSpec.starts(w, Nil{}) == q : Bool}, +j0: Nat, +j: Nat, -l: List<&2, Nat>, e: {RbSpec.put(q, j0, Nil{}) == j <> l : List<&2, Nat>})
  -> {Nat.is_le(j0, j) == True{} : Bool} & {RbSpec.starts(w, List.drop(&2, Nat, Nil{}, Nat.sub(j, j0))) == True{} : Bool}:
  match q:
    case True{}:
      %Equal.cong(List<&2, Nat>, Nat, rb.hd, j0 <> Nil{}, j <> l, e) : {Nat.is_le(j0, _) == True{} : Bool} & {RbSpec.starts(w, Nil{}) == True{} : Bool}
      (rb.le_refl(j0), eq)
    case False{}:
      rb.nil_con({Nat.is_le(j0, j) == True{} : Bool} & {RbSpec.starts(w, Nil{}) == True{} : Bool}, j, l, e)

def rb.cp.fin(+c: Nat, -t: List<&2, Nat>, -w: List<&2, Nat>, +j0: Nat, +j: Nat, both: {Nat.is_le(1n+j0, j) == True{} : Bool} & {RbSpec.starts(w, List.drop(&2, Nat, t, Nat.sub(j, 1n+j0))) == True{} : Bool})
  -> {Nat.is_le(j0, j) == True{} : Bool} & {RbSpec.starts(w, List.drop(&2, Nat, c <> t, Nat.sub(j, j0))) == True{} : Bool}:
  (le1, st) = both
  +l1 = le1
  %Equal.sym(Nat, Nat.sub(j, j0), 1n+Nat.sub(j, 1n+j0), rb.sub_succ(j0, j, l1)) : {Nat.is_le(j0, j) == True{} : Bool} & {RbSpec.starts(w, List.drop(&2, Nat, c <> t, _)) == True{} : Bool}
  (rb.le_of_succ(j0, j, l1), st)

def rb.cp.con(q: Bool, +c: Nat, -t: List<&2, Nat>, -w: List<&2, Nat>, eq: {RbSpec.starts(w, c <> t) == q : Bool}, +j0: Nat, +j: Nat, -l: List<&2, Nat>,
  e: {RbSpec.put(q, j0, RbSpec.copies.go(t, w, 1n+j0)) == j <> l : List<&2, Nat>},
  ih: {RbSpec.copies.go(t, w, 1n+j0) == j <> l : List<&2, Nat>} -> ({Nat.is_le(1n+j0, j) == True{} : Bool} & {RbSpec.starts(w, List.drop(&2, Nat, t, Nat.sub(j, 1n+j0))) == True{} : Bool}))
  -> {Nat.is_le(j0, j) == True{} : Bool} & {RbSpec.starts(w, List.drop(&2, Nat, c <> t, Nat.sub(j, j0))) == True{} : Bool}:
  match q:
    case True{}:
      %Equal.cong(List<&2, Nat>, Nat, rb.hd, j0 <> RbSpec.copies.go(t, w, 1n+j0), j <> l, e) : {Nat.is_le(j0, _) == True{} : Bool} & {RbSpec.starts(w, List.drop(&2, Nat, c <> t, Nat.sub(_, j0))) == True{} : Bool}
      %Equal.sym(Nat, Nat.sub(j0, j0), 0n, rb.sub_self(j0)) : {Nat.is_le(j0, j0) == True{} : Bool} & {RbSpec.starts(w, List.drop(&2, Nat, c <> t, _)) == True{} : Bool}
      (rb.le_refl(j0), eq)
    case False{}:
      rb.cp.fin(c, t, w, j0, j, ih(e))

# a copy found is at or after j0, and the window starts the lines there
def rb.cp.mem(x: List<&2, Nat>, +w: List<&2, Nat>, +j0: Nat, +j: Nat, +l: List<&2, Nat>, e: {RbSpec.copies.go(x, w, j0) == j <> l : List<&2, Nat>})
  -> {Nat.is_le(j0, j) == True{} : Bool} & {RbSpec.starts(w, List.drop(&2, Nat, x, Nat.sub(j, j0))) == True{} : Bool}:
  match x:
    case Nil{}:
      rb.cp.nil(RbSpec.starts(w, Nil{}), w, {==}, j0, j, l, e)
    case Con{+c, +t}:
      rb.cp.con(RbSpec.starts(w, c <> t), c, t, w, {==}, j0, j, l, e, e2 => rb.cp.mem(t, w, 1n+j0, j, l, e2))

def rb.cp.one.fin(-h: List<&2, Nat>, -w: List<&2, Nat>, +j: Nat, both: {Nat.is_le(0n, j) == True{} : Bool} & {RbSpec.starts(w, List.drop(&2, Nat, h, Nat.sub(j, 0n))) == True{} : Bool}) -> {RbSpec.starts(w, List.drop(&2, Nat, h, j)) == True{} : Bool}:
  (z, st) = both
  %rb.sub_zero(j) : {RbSpec.starts(w, List.drop(&2, Nat, h, _)) == True{} : Bool}
  st

# the one copy of w in h starts h's lines at j
def rb.cp.one(+h: List<&2, Nat>, +w: List<&2, Nat>, +j: Nat, e: {RbSpec.copies(h, w) == [j] : List<&2, Nat>}) -> {RbSpec.starts(w, List.drop(&2, Nat, h, j)) == True{} : Bool}:
  rb.cp.one.fin(h, w, j, rb.cp.mem(h, w, 0n, j, Nil{}, e))

# Same lines
# ----------

def rb.same_eq(a: List<&2, Nat>, b: List<&2, Nat>, e: {RbSpec.same(a, b) == True{} : Bool}) -> {a == b : List<&2, Nat>}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, ys}:
      rb.absurdF({Nil{} == y <> ys : List<&2, Nat>}, e)
    case Con{x, xs} Nil{}:
      rb.absurdF({x <> xs == Nil{} : List<&2, Nat>}, e)
    case Con{+x, +xs} Con{+y, +ys}:
      +e0 = e
      %rb.eq_true(x, y, rb.and_l(Nat.is_eq(x, y), RbSpec.same(xs, ys), e0)) : {x <> xs == _ <> ys : List<&2, Nat>}
      %rb.same_eq(xs, ys, rb.and_r(Nat.is_eq(x, y), RbSpec.same(xs, ys), e0)) : {x <> xs == x <> _ : List<&2, Nat>}
      {==}

def rb.pairs_refl(+b: List<&2, Nat>, es: List<&2, R.Edit>) -> {RbSpec.pairs(b, b, es, es) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case Con{+e, rest}:
      %Equal.sym(Bool, RbSpec.same(RbSpec.edit_lines(e), RbSpec.edit_lines(e)), True{}, rb.same_refl(RbSpec.edit_lines(e))) : {Bool.and(Bool.and(_, RbSpec.same(RbSpec.region(b, e), RbSpec.region(b, e))), RbSpec.pairs(b, b, rest, rest)) == True{} : Bool}
      %Equal.sym(Bool, RbSpec.same(RbSpec.region(b, e), RbSpec.region(b, e)), True{}, rb.same_refl(RbSpec.region(b, e))) : {Bool.and(Bool.and(True{}, _), RbSpec.pairs(b, b, rest, rest)) == True{} : Bool}
      rb.pairs_refl(b, rest)
