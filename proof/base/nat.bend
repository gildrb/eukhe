# eukhe: lemmas the proofs of two or more areas share: nat

import Base
import ../../bend/retry.bend as R
import ../../bend/run/state.bend as RnState
import ../../bend/tree.bend as Tr
import ../../laws/command.bend as Command
import ./bool.bend as LBool
import ./logic/bool.bend as LLogicBool
import ./logic/logic.bend as LLogicLogic
import ./logic/nat.bend as LLogicNat

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
      LBool.cb_and_intro(Nat.is_eq(x, x), Command.cmd_eq(xs, xs), cb_nat_refl(x), cb_eq_refl(xs))

def cb_path_refl(a: List<&2, List<&2, Nat>>) -> {Command.cmd_path_eq(a, a) == True{} : Bool}:
  match a:
    case Nil{}:
      {==}
    case Con{+x, +xs}:
      LBool.cb_and_intro(Command.cmd_eq(x, x), Command.cmd_path_eq(xs, xs), cb_eq_refl(x), cb_path_refl(xs))

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
      LLogicLogic.tree.pt.absurdF({Nat.is_eq(a, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      pt.lt_ne(p, q, h)

def pt.lt_ne_r(+a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_eq(b, a) == False{} : Bool}:
  pt.ne_comm(a, b, pt.lt_ne(a, b, h))

def semver.ps.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      semver.ps.eq_refl(p)

def ppr.nat_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      ppr.nat_eq_refl(p)

# Numbers
# -------

def rp.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      rp.eq_refl(p)

def rp.ne_of_lt(+last: Nat, +a: Nat, h: {Nat.is_lt(last, a) == True{} : Bool}) -> {Nat.is_eq(a, last) == False{} : Bool}:
  match last a:
    case 0n 0n:
      LLogicLogic.rp.absurdF({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+p:
      {==}
    case 1n+q 0n:
      LLogicLogic.rp.absurdF({Nat.is_eq(0n, 1n+q) == False{} : Bool}, h)
    case 1n+q 1n+p:
      rp.ne_of_lt(q, p, h)

def wn_le_step(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.wn_absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)
    case 1n+p 1n+q:
      wn_le_step(p, q, h)

def wn_le_trans(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool})
  -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      {==}
    case 0n 0n 1n+z:
      {==}
    case 0n 1n+y 0n:
      {==}
    case 0n 1n+y 1n+z:
      {==}
    case 1n+x 0n 0n:
      LLogicLogic.wn_absurd({Nat.is_le(1n+x, 0n) == True{} : Bool}, h1)
    case 1n+x 0n 1n+z:
      LLogicLogic.wn_absurd({Nat.is_le(1n+x, 1n+z) == True{} : Bool}, h1)
    case 1n+x 1n+y 0n:
      LLogicLogic.wn_absurd({Nat.is_le(1n+x, 0n) == True{} : Bool}, h2)
    case 1n+x 1n+y 1n+z:
      wn_le_trans(x, y, z, h1, h2)

def wn_le_add(+k: Nat, +a: Nat, +b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, Nat.add(k, b)) == True{} : Bool}:
  match k:
    case 0n:
      h
    case 1n+j:
      wn_le_step(a, Nat.add(j, b), wn_le_add(j, a, b, h))

# Numbers
# -------

def compactor.pc.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def compactor.pc.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      compactor.pc.le_refl(p)

def pc.lt_not_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      LLogicLogic.pc.absurd_ft({True{} == False{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.pc.absurd_ft({True{} == False{} : Bool}, e)
    case 1n+p 1n+q:
      pc.lt_not_le(p, q, e)

def pc.le_succ_r(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n q:
      {==}
    case 1n+p 0n:
      LLogicLogic.pc.absurd_ft({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_succ_r(p, q, e)

def compactor.pc.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n q r:
      compactor.pc.le_zero(r)
    case 1n+p 0n r:
      LLogicLogic.pc.absurd_ft({Nat.is_le(1n+p, r) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LLogicLogic.pc.absurd_ft({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      compactor.pc.le_trans(p, q, r, ab, bc)

# m <= n + m
def compactor.pc.le_add(n: Nat, +m: Nat) -> {Nat.is_le(m, Nat.add(n, m)) == True{} : Bool}:
  match n:
    case 0n:
      compactor.pc.le_refl(m)
    case 1n+p:
      +q = p
      pc.le_succ_r(m, Nat.add(q, m), compactor.pc.le_add(q, m))

def child.pc.le_zero(+b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+q:
      {==}

def child.pc.le_refl(+a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      child.pc.le_refl(p)

def pc.le_succ(+a: Nat, +b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      LLogicLogic.child.pc.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_succ(p, q, e)

def child.pc.le_trans(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      child.pc.le_zero(c)
    case 1n+p 0n c:
      LLogicLogic.child.pc.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LLogicLogic.child.pc.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      child.pc.le_trans(p, q, r, ab, bc)

def pc.sub_le(+a: Nat, +d: Nat) -> {Nat.is_le(Nat.sub(a, d), a) == True{} : Bool}:
  match a d:
    case 0n d:
      {==}
    case 1n+p 0n:
      child.pc.le_refl(p)
    case 1n+p 1n+e:
      pc.le_succ(Nat.sub(p, e), p, pc.sub_le(p, e))

def child.pc.le_add(+c: Nat, +x: Nat) -> {Nat.is_le(x, Nat.add(c, x)) == True{} : Bool}:
  match c:
    case 0n:
      child.pc.le_refl(x)
    case 1n+p:
      pc.le_succ(x, Nat.add(p, x), child.pc.le_add(p, x))

# Arithmetic
# ----------

def pj.le0(t: Nat) -> {Nat.is_le(0n, t) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      {==}

def pj.min_le_r(n: Nat, m: Nat) -> {Nat.is_le(Nat.min(n, m), m) == True{} : Bool}:
  match n m:
    case 0n _:
      pj.le0(m)
    case 1n+np 0n:
      {==}
    case 1n+np 1n+mp:
      pj.min_le_r(np, mp)

def pi.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pi.le_add(+a: Nat, +s: Nat) -> {Nat.is_le(a, Nat.add(a, s)) == True{} : Bool}:
  match a:
    case 0n:
      pi.le0(s)
    case 1n+p:
      pi.le_add(p, s)

def pi.lt_nle(+a: Nat, +b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      LLogicLogic.pi.absurdF({Nat.is_le(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.pi.absurdF({Nat.is_le(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      pi.lt_nle(p, q, h)

def pq.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def ps.le0(t: Nat) -> {Nat.is_le(0n, t) == True{} : Bool}:
  match t:
    case 0n:
      {==}
    case 1n+q:
      {==}

def screen.ps.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      screen.ps.le_refl(p)

def screen.ps.le_succ(n: Nat) -> {Nat.is_le(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      screen.ps.le_succ(p)

def screen.ps.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      ps.le0(c)
    case 1n+ap 0n _:
      LLogicLogic.screen.ps.absurdF({Nat.is_le(1n+ap, c) == True{} : Bool}, ab)
    case 1n+ap 1n+bp 0n:
      LLogicLogic.screen.ps.absurdF({Nat.is_le(1n+ap, 0n) == True{} : Bool}, bc)
    case 1n+ap 1n+bp 1n+cp:
      screen.ps.le_trans(ap, bp, cp, ab, bc)

# Numbers
# -------

def supervisor.ps.le_refl(a: Nat) -> {Nat.is_le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      supervisor.ps.le_refl(p)

def ps.le_zero(b: Nat) -> {Nat.is_le(0n, b) == True{} : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      {==}

def supervisor.ps.le_succ(a: Nat) -> {Nat.is_le(a, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      supervisor.ps.le_succ(p)

def supervisor.ps.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      ps.le_zero(c)
    case 1n+p 0n _:
      LLogicLogic.supervisor.ps.absurdF({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LLogicLogic.supervisor.ps.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      supervisor.ps.le_trans(p, q, r, ab, bc)

# x is at most g + x
def supervisor.ps.le_add_l(+g: Nat, +x: Nat) -> {Nat.is_le(x, Nat.add(g, x)) == True{} : Bool}:
  match g:
    case 0n:
      supervisor.ps.le_refl(x)
    case 1n+p:
      supervisor.ps.le_trans(x, Nat.add(p, x), 1n+Nat.add(p, x), supervisor.ps.le_add_l(p, x), supervisor.ps.le_succ(Nat.add(p, x)))

# adding g on the left keeps the order
def ps.le_mono(g: Nat, -a: Nat, -x: Nat, h: {Nat.is_le(a, x) == True{} : Bool}) -> {Nat.is_le(Nat.add(g, a), Nat.add(g, x)) == True{} : Bool}:
  match g:
    case 0n:
      h
    case 1n+p:
      ps.le_mono(p, a, x, h)

# Numbers
# -------

def pu.le_zero(+n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pu.le_refl(+n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pu.le_refl(p)

def pu.le_trans(+a: Nat, +b: Nat, +c: Nat, +ab: {Nat.is_le(a, b) == True{} : Bool}, +bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n q r:
      pu.le_zero(r)
    case 1n+p 0n r:
      LLogicLogic.pu.absurd_ft({Nat.is_le(1n+p, r) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LLogicLogic.pu.absurd_ft({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      pu.le_trans(p, q, r, ab, bc)

def pu.le_succ_r(+a: Nat, +b: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n q:
      {==}
    case 1n+p 0n:
      LLogicLogic.pu.absurd_ft({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pu.le_succ_r(p, q, e)

# a <= a + c
def pu.le_add_r(+a: Nat, +c: Nat) -> {Nat.is_le(a, Nat.add(a, c)) == True{} : Bool}:
  match a:
    case 0n:
      pu.le_zero(c)
    case 1n+p:
      pu.le_add_r(p, c)

# z <= x - n when n + z <= x
def pu.le_sub(+n: Nat, +z: Nat, +x: Nat, +e: {Nat.is_le(Nat.add(n, z), x) == True{} : Bool}) -> {Nat.is_le(z, Nat.sub(x, n)) == True{} : Bool}:
  match n x:
    case 0n 0n:
      e
    case 0n 1n+q:
      e
    case 1n+p 0n:
      LLogicLogic.pu.absurd_ft({Nat.is_le(z, Nat.sub(0n, 1n+p)) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pu.le_sub(p, z, q, e)

def pu.le_add_left(+n: Nat, +z: Nat, +x: Nat, +e: {Nat.is_le(Nat.add(n, z), x) == True{} : Bool}) -> {Nat.is_le(n, x) == True{} : Bool}:
  pu.le_trans(n, Nat.add(n, z), x, pu.le_add_r(n, z), e)

def pu.sub_le_self(+x: Nat, +n: Nat) -> {Nat.is_le(Nat.sub(x, n), x) == True{} : Bool}:
  match x n:
    case 0n q:
      {==}
    case 1n+p 0n:
      pu.le_refl(1n+p)
    case 1n+p 1n+q:
      pu.le_succ_r(Nat.sub(p, q), p, pu.sub_le_self(p, q))

# x - n <= f when x <= 1 + f and n >= 1
def pu.sub_fuel(+x: Nat, +f: Nat, +n: Nat, +ex: {Nat.is_le(x, 1n+f) == True{} : Bool}, +en: {Nat.is_le(1n, n) == True{} : Bool}) -> {Nat.is_le(Nat.sub(x, n), f) == True{} : Bool}:
  match x n:
    case p 0n:
      LLogicLogic.pu.absurd_ft({Nat.is_le(Nat.sub(p, 0n), f) == True{} : Bool}, en)
    case 0n 1n+q:
      pu.le_zero(f)
    case 1n+p 1n+q:
      pu.le_trans(Nat.sub(p, q), p, f, pu.sub_le_self(p, q), ex)

def rp.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

def rp.min_le(+a: Nat, +b: Nat) -> {Nat.is_le(Nat.min(a, b), a) == True{} : Bool}:
  match a b:
    case 0n b:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      rp.min_le(p, q)

# (H2) The settle
# ---------------

def pc.lt_to_le(a: Nat, b: Nat, e: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_le(a, b) == True{} : Bool}:
  match a b:
    case p 0n:
      LLogicLogic.pc.lt_zero({Nat.is_le(p, 0n) == True{} : Bool}, p, e)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      pc.lt_to_le(p, q, e)

def pc.le_lt_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case p q 0n:
      LLogicLogic.pc.lt_zero({Nat.is_lt(p, 0n) == True{} : Bool}, q, bc)
    case 0n q 1n+r:
      {==}
    case 1n+p 0n 1n+r:
      LLogicLogic.pc.absurd_ft({Nat.is_lt(1n+p, 1n+r) == True{} : Bool}, ab)
    case 1n+p 1n+q 1n+r:
      pc.le_lt_trans(p, q, r, ab, bc)

def pt.lt_irrefl(k: Nat) -> {Nat.is_lt(k, k) == False{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      pt.lt_irrefl(p)

# Numbers

def tc.lt_le(a: Nat, b: Nat, c: Nat, +ab: {Nat.is_lt(a, b) == True{} : Bool}, +cb: {Nat.is_lt(c, b) == False{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case _ 0n _:
      LLogicLogic.tree.pt.absurdF({Nat.is_lt(a, c) == True{} : Bool}, ab)
    case _ 1n+q 0n:
      LLogicLogic.pt.absurd({Nat.is_lt(a, 0n) == True{} : Bool}, cb)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 1n+q 1n+r:
      tc.lt_le(p, q, r, ab, cb)

def tc.lt_asym(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case _ 0n:
      LLogicLogic.tree.pt.absurdF({Nat.is_lt(0n, a) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      tc.lt_asym(p, q, h)

def tc.lt_total(a: Nat, b: Nat, +nl: {Nat.is_lt(a, b) == False{} : Bool}, +ne: {Nat.is_eq(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      LLogicLogic.pt.absurd({Nat.is_lt(0n, 0n) == True{} : Bool}, ne)
    case 0n 1n+q:
      LLogicLogic.pt.absurd({Nat.is_lt(1n+q, 0n) == True{} : Bool}, nl)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      tc.lt_total(p, q, nl, ne)

def tc.lt_head(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {LLogicBool.tc.lt(e <> r, b) == True{} : Bool}) -> {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}:
  LLogicBool.tree.pt.and_l(Nat.is_lt(Tr.Ent.k(e), b), LLogicBool.tc.lt(r, b), h)

def tc.ge_head(+e: Tr.Ent, +r: List<&2, Tr.Ent>, +b: Nat, +h: {LLogicBool.tc.ge(e <> r, b) == True{} : Bool}) -> {Nat.is_lt(Tr.Ent.k(e), b) == False{} : Bool}:
  LLogicBool.pt.not_f(Nat.is_lt(Tr.Ent.k(e), b), LLogicBool.tree.pt.and_l(Bool.not(Nat.is_lt(Tr.Ent.k(e), b)), LLogicBool.tc.ge(r, b), h))

# a key at or above b is no key of a list below b
def tc.lt_miss(+e: Tr.Ent, +b: Nat, +x: Nat, +lk: {Nat.is_lt(Tr.Ent.k(e), b) == True{} : Bool}, +xb: {Nat.is_lt(x, b) == False{} : Bool}) -> {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}:
  pt.lt_ne(Tr.Ent.k(e), x, tc.lt_le(Tr.Ent.k(e), b, x, lk, xb))

# a key below b is no key of a list at or above b
def tc.ge_miss(+e: Tr.Ent, +b: Nat, +x: Nat, +ge: {Nat.is_lt(Tr.Ent.k(e), b) == False{} : Bool}, +xb: {Nat.is_lt(x, b) == True{} : Bool}) -> {Nat.is_eq(Tr.Ent.k(e), x) == False{} : Bool}:
  pt.lt_ne_r(x, Tr.Ent.k(e), tc.lt_le(x, b, Tr.Ent.k(e), xb, ge))

# ---- director ----

# proof_director: the Director stack laws (S5), about bend/director.bend.
#
# The bound: a decision under `above` layers keeps above + len(stack) at
# most cap (`pd.go_bounded`), with room telling whether above + len(s)
# is below cap (the whole stack's length, fixed for the decision). A
# layer that keeps its place keeps the length; a deferring layer, or one
# that leads and stays, goes back on the stack of the layers below
# (`pd.under_ok`), which is bounded under one more layer; a Leave, or a
# Lead that leaves, drops it (`pd.le_pred`); a Stack adds a layer only
# with room (`pd.push_ok`). Each loop step is one decision, and its kept
# stack (leads staying) is a decision too (`pd.tick_bounded`).
#
# The loop: `pd.ok(l, k)` says the loop has ended, or has fewer than k
# global steps left. A tick takes one step off (`pd.tick_ok`), so after k
# steps the loop has ended (`pd.ends_go`). An ended loop never changes.
#
# The rule: each verdict law unfolds decide.go once (`pd.on_top` matches
# the model's `under` with the spec's `dir_on_top`); each tick law settles
# one outcome (`pd.settle_cont0`, `pd.settle_hand`, `pd.settle_failed`).
#
# Leads: a decision where leads leave equals the decision on the verdicts
# with each Lead read as a Leave (`pd.leave_as`), one where they stay the
# decision with each read as a Defer (`pd.defer_as`), and both have the
# same outcome (`pd.out_stay`). A step that goes on does not read the kept
# stack (`pd.settle_on`); one that ends reads only the outcome and the
# kept stack (`pd.settle_end`).
#
# The tree: layer i of a stack (0 = bottom) is the nodes 2i + 1 and
# 2i + 2, appended after the nodes of the layers below. So every key of
# encode(s) is at most 2 len(s) (`pd.enc_lt`), the nodes stay sorted
# (`pd.enc_sorted`), and each kind node hangs under the root or the kind
# node of the layer below (`pd.parent_ok`), each budget node under its
# kind node (`pd.enc_rooted`). decode reads the pairs back in order
# (`pd.dec_go`), and a rewind reaches the encoded tree (proof_tree's
# `rewind_reaches`), so it restores the stack.

# Numbers
# -------

def pd.lt_succ(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      pd.lt_succ(p)

def pu.lt_zero_f(+q: Nat) -> {False{} == Nat.is_lt(q, 0n) : Bool}:
  match q:
    case 0n:
      {==}
    case 1n+p:
      {==}

def rp.lt_succ(+last: Nat, +a: Nat, h: {Nat.is_lt(last, a) == True{} : Bool}) -> {Nat.is_lt(last, 1n+a) == True{} : Bool}:
  match last a:
    case 0n a:
      {==}
    case 1n+q 0n:
      LLogicLogic.rp.absurdF({Nat.is_lt(1n+q, 1n) == True{} : Bool}, h)
    case 1n+q 1n+p:
      rp.lt_succ(q, p, h)

def rp.lt_self(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      rp.lt_self(p)

def tc.cmp_lt(a: Nat, b: Nat, +h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.cmp(a, b) == LT{} : Cmp}:
  match a b:
    case _ 0n:
      LLogicLogic.tree.pt.absurdF({Nat.cmp(a, 0n) == LT{} : Cmp}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 1n+q:
      tc.cmp_lt(p, q, h)

def tc.cmp_gt(a: Nat, b: Nat, +h: {Nat.is_lt(b, a) == True{} : Bool}) -> {Nat.cmp(a, b) == GT{} : Cmp}:
  match a b:
    case 0n 0n:
      LLogicLogic.tree.pt.absurdF({Nat.cmp(0n, 0n) == GT{} : Cmp}, h)
    case 0n 1n+q:
      LLogicLogic.tree.pt.absurdF({Nat.cmp(0n, 1n+q) == GT{} : Cmp}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      tc.cmp_gt(p, q, h)

def tc.cmp_eq(a: Nat, b: Nat, +h: {Nat.is_eq(a, b) == True{} : Bool}) -> {Nat.cmp(a, b) == EQ{} : Cmp}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.tree.pt.absurdF({Nat.cmp(0n, 1n+q) == EQ{} : Cmp}, h)
    case 1n+p 0n:
      LLogicLogic.tree.pt.absurdF({Nat.cmp(1n+p, 0n) == EQ{} : Cmp}, h)
    case 1n+p 1n+q:
      tc.cmp_eq(p, q, h)

def pj.sub_zero(c: Nat) -> {c == Nat.sub(c, 0n) : Nat}:
  match c:
    case 0n:
      {==}
    case 1n+p:
      {==}

def pj.min_of_le(n: Nat, m: Nat, h: {Nat.is_le(n, m) == True{} : Bool}) -> {n == Nat.min(n, m) : Nat}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      LLogicLogic.pj.absurdF({1n+np == Nat.min(1n+np, 0n) : Nat}, h)
    case 1n+np 1n+mp:
      %pj.min_of_le(np, mp, h) : {1n+np == 1n+_ : Nat}
      {==}

def rp.ge_move(-a: Nat, -b: Nat, +c: Nat, e: {a == b : Nat}, h: {Nat.is_ge(a, c) == True{} : Bool}) -> {Nat.is_ge(b, c) == True{} : Bool}:
  %e : {Nat.is_ge(_, c) == True{} : Bool}
  h

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

def wn_le_k(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.add(a, LLogicNat.wn_sub(b, a)) == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.wn_absurd({Nat.add(1n+p, 0n) == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, k => 1n+k, Nat.add(p, LLogicNat.wn_sub(q, p)), q, wn_le_k(p, q, h))

def pa.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      LLogicNat.pa.succ(Nat.add(p, 0n), p, pa.add_zero(p))

def pa.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      LLogicNat.pa.succ(Nat.add(p, 1n+b), 1n+Nat.add(p, b), pa.add_succ(p, b))

def pa.add_comm(+a: Nat, +b: Nat) -> {Nat.add(a, b) == Nat.add(b, a) : Nat}:
  match a:
    case 0n:
      Equal.sym(Nat, Nat.add(b, 0n), b, pa.add_zero(b))
    case 1n+p:
      Equal.trans(Nat, 1n+Nat.add(p, b), 1n+Nat.add(b, p), Nat.add(b, 1n+p), LLogicNat.pa.succ(Nat.add(p, b), Nat.add(b, p), pa.add_comm(p, b)), Equal.sym(Nat, Nat.add(b, 1n+p), 1n+Nat.add(b, p), pa.add_succ(b, p)))

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

def call_end(+P: Nat, +U: Nat, +r: Nat, +c: Nat, +u: Nat, +p: Nat) -> {Nat.add(LLogicNat.gen(P, RnState.Call{}, c, u, p), 1n+LLogicNat.X(P, U, r)) == Nat.add(LLogicNat.K.call_end(P, U, r, c, u, p), 1n+0n) : Nat}:
  to_end(LLogicNat.gen(P, RnState.Call{}, c, u, p), LLogicNat.X(P, U, r))

def succ_m(+j: Nat, +g: Nat, +X: Nat) -> {Nat.add(j, Nat.add(g, 1n+X)) == 1n+Nat.add(j, Nat.add(g, X)) : Nat}:
  %add_succ_r(g, X) : {Nat.add(j, _) == 1n+Nat.add(j, Nat.add(g, X)) : Nat}
  add_succ(j, Nat.add(g, X))

# a live run may still take an input
def pos(-T: Type, +j: Nat, +g: Nat, +X: Nat, h: {0n == Nat.add(j, Nat.add(g, 1n+X)) : Nat}) -> T:
  LLogicLogic.zero_succ(T, Nat.add(j, Nat.add(g, X)), Equal.trans(Nat, 0n, Nat.add(j, Nat.add(g, 1n+X)), 1n+Nat.add(j, Nat.add(g, X)), h, succ_m(j, g, X)))

def next_len1(-n: Nat, +j: Nat, +k: Nat, -ms: Nat, -mt: Nat, h: {1n+n == Nat.add(j, ms) : Nat}, eq: {ms == Nat.add(k, 1n+mt) : Nat}) -> {1n+n == 1n+Nat.add(Nat.add(j, k), mt) : Nat}:
  %add_succ(Nat.add(j, k), mt) : {1n+n == _ : Nat}
  %add_assoc_r(j, k, 1n+mt) : {1n+n == _ : Nat}
  %eq : {1n+n == Nat.add(j, _) : Nat}
  h

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
      LLogicLogic.pu.absurd_ft({Nat.add(1n+p, Nat.sub(0n, 1n+p)) == 0n : Nat}, e)
    case 1n+p 1n+q:
      %pu.sub_add(p, q, e) : {1n+Nat.add(p, Nat.sub(q, p)) == 1n+_ : Nat}
      {==}

def rp.fresh_good(m: Maybe<&2, R.Switch>, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, +hf: {LLogicBool.rp.fresh_ok(m, last, ts) == True{} : Bool}, elast: {last == R.last_at(ts) : Nat}, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == True{} : Bool}) -> LLogicLogic.rp.Good(m, len, ts, p):
  match m:
    case None{}:
      LLogicLogic.rp.good_none(len, ts, p)
    case Some{s}:
      match s:
        case R.Switch{+to, d}:
          match d:
            case 0n:
              nl = LLogicBool.rp.and_l(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts)), hf)
              +fr = LLogicBool.rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.not(R.seen(to, ts)), hf)
              nl2 = LBool.rp.not_eq_move(to, last, R.last_at(ts), elast, nl)
              ff = LBool.rp.or_l(Bool.not(R.seen(to, ts)), R.all_seen(len, ts), fr)
              rw = LBool.rp.or_l(Bool.not(R.seen(to, ts)), Bool.and(Nat.is_gt(0n, 0n), Nat.is_ge(0n, R.server(to, ts))), fr)
              (nl2, (ff, (rw, (rp.le_zero(R.Policy.max(p)), eok))))
            case 1n+k:
              LLogicLogic.rp.absurdF(LLogicLogic.rp.Good(Some{R.Switch{to, 1n+k}}, len, ts, p), hf)

def rp.back_good(m: Maybe<&2, R.Switch>, +last: Nat, +len: Nat, +ts: List<&2, R.Tried>, +p: R.Policy, +backoff: Nat, +hb: {LLogicBool.rp.back_ok(m, last, ts, backoff, R.Policy.max(p)) == True{} : Bool}, eall: {R.all_seen(len, ts) == True{} : Bool}, elast: {last == R.last_at(ts) : Nat}, eok: {Nat.is_le(R.length(ts), R.Policy.switches(p)) == True{} : Bool}) -> LLogicLogic.rp.Good(m, len, ts, p):
  match m:
    case None{}:
      LLogicLogic.rp.good_none(len, ts, p)
    case Some{s}:
      match s:
        case R.Switch{+to, +d}:
          +rest = LLogicBool.rp.and_r(Nat.is_eq(Nat.max(backoff, R.server(to, ts)), d), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)))), hb)
          deq = LLogicNat.rp.eq_true(Nat.max(backoff, R.server(to, ts)), d, LLogicBool.rp.and_l(Nat.is_eq(Nat.max(backoff, R.server(to, ts)), d), Bool.and(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)))), hb))
          nl = LLogicBool.rp.and_l(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p))), rest)
          +wc = LLogicBool.rp.and_r(Bool.not(Nat.is_eq(to, last)), Bool.and(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p))), rest)
          pos = LLogicBool.rp.and_l(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)), wc)
          cap = LLogicBool.rp.and_r(Nat.is_gt(d, 0n), Nat.is_le(d, R.Policy.max(p)), wc)
          nl2 = LBool.rp.not_eq_move(to, last, R.last_at(ts), elast, nl)
          ge = rp.ge_move(Nat.max(backoff, R.server(to, ts)), d, R.server(to, ts), deq, Nat.max_ge_r(backoff, R.server(to, ts)))
          ff = LBool.rp.or_r(Bool.not(R.seen(to, ts)), R.all_seen(len, ts), eall)
          rw = LBool.rp.or_r(Bool.not(R.seen(to, ts)), Bool.and(Nat.is_gt(d, 0n), Nat.is_ge(d, R.server(to, ts))), LBool.rp.and_tt(Nat.is_gt(d, 0n), Nat.is_ge(d, R.server(to, ts)), pos, ge))
          (nl2, (ff, (rw, (cap, eok))))
