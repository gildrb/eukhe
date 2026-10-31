# eukhe: lemmas the proofs of area cron_file share: Bools and Nats

import Base

def cfl.If(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      A

def cfl.IfF(b: Bool, A: Type) -> Type:
  match b:
    case True{}:
      A
    case False{}:
      Unit

# True is not False
def cfl.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : cfl.If(_, A)
  Unit{}

def cfl.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : cfl.IfF(_, A)
  Unit{}

def cfl.eq_comm(a: Nat, b: Nat) -> {Nat.is_eq(a, b) == Nat.is_eq(b, a) : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      cfl.eq_comm(p, q)

def cfl.eq_refl(k: Nat) -> {Nat.is_eq(k, k) == True{} : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      cfl.eq_refl(p)

def cfl.eq_of(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      cfl.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      cfl.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      +e = cfl.eq_of(p, q, h)
      %e : {1n+p == 1n+_ : Nat}
      {==}

def cfl.and_comm(a: Bool, b: Bool) -> {Bool.and(a, b) == Bool.and(b, a) : Bool}:
  match a b:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def cfl.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      cfl.absurdF({False{} == True{} : Bool}, e)

def cfl.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      cfl.absurdF({b == True{} : Bool}, e)

def cfl.or_false_l(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      cfl.absurd({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def cfl.or_false_r(a: Bool, -b: Bool, e: {Bool.or(a, b) == False{} : Bool}) -> {b == False{} : Bool}:
  match a:
    case True{}:
      cfl.absurd({b == False{} : Bool}, e)
    case False{}:
      e

def cfl.not_true(a: Bool, e: {Bool.not(a) == True{} : Bool}) -> {a == False{} : Bool}:
  match a:
    case True{}:
      cfl.absurdF({True{} == False{} : Bool}, e)
    case False{}:
      {==}

# a == b and b == c give a == c for Bools at False: is_eq(x, i) is False
# when is_eq(i, x) is
def cfl.ne_comm(i: Nat, x: Nat, e: {Nat.is_eq(i, x) == False{} : Bool}) -> {Nat.is_eq(x, i) == False{} : Bool}:
  %cfl.eq_comm(i, x) : {_ == False{} : Bool}
  e
