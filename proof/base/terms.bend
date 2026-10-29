# eukhe: lemmas the proofs of two or more areas share: Bool and Nat terms
# against the laws' Bool, both ways.

import Base
import ./logic/logic.bend as LLogicLogic

def lt.absurd(-A: Type, e: {False{} == True{} : Bool}) -> A:
  LLogicLogic.pj.absurdF(A, e)

def lt.eq_refl(n: Nat) -> {True{} == Nat.is_eq(n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      lt.eq_refl(p)

def lt.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      lt.absurd({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      lt.absurd({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      %lt.eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}

def lt.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def lt.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      lt.absurd({b == True{} : Bool}, h)

def lt.or_l(a: Bool, -b: Bool, h: {a == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      lt.absurd({Bool.or(False{}, b) == True{} : Bool}, h)

def lt.or_r(a: Bool, -b: Bool, h: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      h

def lt.or_cases(a: Bool, -b: Bool, h: {Bool.or(a, b) == True{} : Bool}) -> Or({a == True{} : Bool}, {b == True{} : Bool}):
  match a:
    case True{}:
      Inl{{==}}
    case False{}:
      Inr{h}

def lt.not_true(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      lt.absurd({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def lt.or_elim(-A: Type, -B: Type, -C: Type, o: Or(A, B), f: A -> C, g: B -> C) -> C:
  match o:
    case Inl{a}:
      f(a)
    case Inr{b}:
      g(b)
