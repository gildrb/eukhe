# eukhe: lemmas the proofs of two or more areas share: nat/is_eq

import Base
import ../../../laws/command.bend as Command
import ../bool/and.bend as LBoolAnd
import ../bool/misc.bend as LBoolMisc

# Equality of chars, names, paths
# -------------------------------

def cb_nat_eq(+x: Nat, +y: Nat, e: {Nat.is_eq(x, y) == True{} : Bool}) -> {x == y : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LBoolMisc.cb_absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      LBoolMisc.cb_absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %cb_nat_eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def cb_nat_refl(x: Nat) -> {Nat.is_eq(x, x) == True{} : Bool}:
  match x:
    case 0n:
      {==}
    case 1n+p:
      cb_nat_refl(p)

def cb_eq_refl(a: List<&2, Nat>) -> {Command.cmd_eq(a, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +xs}:
      LBoolAnd.cb_and_intro(Nat.is_eq(x, x), Command.cmd_eq(xs, xs), cb_nat_refl(x), cb_eq_refl(xs))

def cb_path_refl(a: List<&2, List<&2, Nat>>) -> {Command.cmd_path_eq(a, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +xs}:
      LBoolAnd.cb_and_intro(Command.cmd_eq(x, x), Command.cmd_path_eq(xs, xs), cb_eq_refl(x), cb_path_refl(xs))

# Node equality is reflexive
# --------------------------

def pf.nat_eq_refl(n: Nat) -> {True{} == Nat.is_eq(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pf.nat_eq_refl(p)

# Numbers
# -------

def child.pc.eq_refl(+a: Nat) -> {Nat.is_eq(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      child.pc.eq_refl(p)

def pc.eq_succ(+a: Nat) -> {Nat.is_eq(1n+a, a) == False{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      pc.eq_succ(p)

def child.pc.eq_of(+a: Nat, +b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LBoolMisc.child.pc.absurd({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      LBoolMisc.child.pc.absurd({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      %child.pc.eq_of(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

def pt.eq_comm(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      pt.eq_comm(p, q)

def pt.ne_comm(+a: Nat, +b: Nat, h: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  %pt.eq_comm(a, b) : {_ == False{} : Bool}
  h

# a key below another is not it
def pt.lt_ne(a: Nat, b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match a b:
    case _ 0n:
      LBoolMisc.tree.pt.absurdF({Nat.is_eq(a, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      pt.lt_ne(p, q, h)

def pt.lt_ne_r(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  pt.ne_comm(a, b, pt.lt_ne(a, b, h))

def pq.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LBoolMisc.pq.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LBoolMisc.pq.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, pq.eq_true(p, q, h))

def semver.ps.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      semver.ps.eq_refl(p)

def semver.ps.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LBoolMisc.semver.ps.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LBoolMisc.semver.ps.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, semver.ps.eq_true(p, q, h))

def ppr.nat_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ppr.nat_eq_refl(p)

def ppr.nat_eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LBoolMisc.ppr.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LBoolMisc.ppr.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, ppr.nat_eq_true(p, q, h))

def supervisor.ps.eq_of_is_eq(a: Nat, b: Nat, e: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LBoolMisc.supervisor.ps.absurdF({0n == 1n+q : Nat}, e)
    case 1n+p 0n:
      LBoolMisc.supervisor.ps.absurdF({1n+p == 0n : Nat}, e)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, supervisor.ps.eq_of_is_eq(p, q, e))

# Numbers
# -------

def rp.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      rp.eq_refl(p)

def rp.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LBoolMisc.rp.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LBoolMisc.rp.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, rp.eq_true(p, q, h))

def rp.ne_of_lt(+last: Nat, +a: Nat, h: {Nat.is_lt(last, a) == True{} : Bool}) -> {Nat.is_eq(a, last) == False{} : Bool}:
  match last a:
    case 0n 0n:
      LBoolMisc.rp.absurdF({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+p:
      {==}
    case 1n+q 0n:
      LBoolMisc.rp.absurdF({Nat.is_eq(0n, 1n+q) == False{} : Bool}, h)
    case 1n+q 1n+p:
      rp.ne_of_lt(q, p, h)
