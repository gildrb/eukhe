# eukhe: lemmas the proofs of two or more areas share: nat/is_le

import Base
import ../bool/misc.bend as LBoolMisc

def wn_le_step(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LBoolMisc.wn_absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, h)
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
      LBoolMisc.wn_absurd({Nat.is_le(1n+x, 0n) == True{} : Bool}, h1)
    case 1n+x 0n 1n+z:
      LBoolMisc.wn_absurd({Nat.is_le(1n+x, 1n+z) == True{} : Bool}, h1)
    case 1n+x 1n+y 0n:
      LBoolMisc.wn_absurd({Nat.is_le(1n+x, 0n) == True{} : Bool}, h2)
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
      LBoolMisc.pc.absurd_ft({True{} == False{} : Bool}, e)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LBoolMisc.pc.absurd_ft({True{} == False{} : Bool}, e)
    case 1n+p 1n+q:
      pc.lt_not_le(p, q, e)

def pc.le_succ_r(a: Nat, b: Nat, e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n q:
      {==}
    case 1n+p 0n:
      LBoolMisc.pc.absurd_ft({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_succ_r(p, q, e)

def compactor.pc.le_trans(a: Nat, b: Nat, c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n q r:
      compactor.pc.le_zero(r)
    case 1n+p 0n r:
      LBoolMisc.pc.absurd_ft({Nat.is_le(1n+p, r) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LBoolMisc.pc.absurd_ft({False{} == True{} : Bool}, bc)
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
      LBoolMisc.child.pc.absurd({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
    case 1n+p 1n+q:
      pc.le_succ(p, q, e)

def child.pc.le_trans(+a: Nat, +b: Nat, +c: Nat, ab: {Nat.is_le(a, b) == True{} : Bool}, bc: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_le(a, c) == True{} : Bool}:
  match a b c:
    case 0n b c:
      child.pc.le_zero(c)
    case 1n+p 0n c:
      LBoolMisc.child.pc.absurd({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LBoolMisc.child.pc.absurd({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
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

# j < n and j = n at once
def pc.lt_ne(-A: Type, +j: Nat, +n: Nat, lt: {Nat.is_le(1n+j, n) == True{} : Bool}, eq: {Nat.is_eq(j, n) == True{} : Bool}) -> A:
  match j n:
    case 0n 0n:
      LBoolMisc.child.pc.absurd(A, lt)
    case 0n 1n+q:
      LBoolMisc.child.pc.absurd(A, eq)
    case 1n+p 0n:
      LBoolMisc.child.pc.absurd(A, eq)
    case 1n+p 1n+q:
      pc.lt_ne(A, p, q, lt, eq)

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
      LBoolMisc.pi.absurdF({Nat.is_le(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LBoolMisc.pi.absurdF({Nat.is_le(0n, 1n+p) == False{} : Bool}, h)
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
      LBoolMisc.screen.ps.absurdF({Nat.is_le(1n+ap, c) == True{} : Bool}, ab)
    case 1n+ap 1n+bp 0n:
      LBoolMisc.screen.ps.absurdF({Nat.is_le(1n+ap, 0n) == True{} : Bool}, bc)
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
      LBoolMisc.supervisor.ps.absurdF({Nat.is_le(1n+p, c) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LBoolMisc.supervisor.ps.absurdF({Nat.is_le(1n+p, 0n) == True{} : Bool}, bc)
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
      LBoolMisc.pu.absurd_ft({Nat.is_le(1n+p, r) == True{} : Bool}, ab)
    case 1n+p 1n+q 0n:
      LBoolMisc.pu.absurd_ft({False{} == True{} : Bool}, bc)
    case 1n+p 1n+q 1n+r:
      pu.le_trans(p, q, r, ab, bc)

def pu.le_succ_r(+a: Nat, +b: Nat, +e: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_le(a, 1n+b) == True{} : Bool}:
  match a b:
    case 0n q:
      {==}
    case 1n+p 0n:
      LBoolMisc.pu.absurd_ft({Nat.is_le(1n+p, 1n) == True{} : Bool}, e)
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
      LBoolMisc.pu.absurd_ft({Nat.is_le(z, Nat.sub(0n, 1n+p)) == True{} : Bool}, e)
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
      LBoolMisc.pu.absurd_ft({Nat.is_le(Nat.sub(p, 0n), f) == True{} : Bool}, en)
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
