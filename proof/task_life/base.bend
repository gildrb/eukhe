# eukhe: lemmas shared by the proofs of area task_life: refuted premises,
# Some's injectivity, and the flags and counts of the join's lists

import Base
import ../../bend/task_life.bend as Tl
import ../../spec/durable/task_life.bend as Sp

# Logic
# -----

def tlb.IfT(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      Unit
    case False{}:
      G

def tlb.IfF(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

# a premise True == False proves anything
def tlb.absurd_tf(-G: Type, e: {True{} == False{} : Bool}) -> G:
  %e : tlb.IfT(_, G)
  Unit{}

# a premise False == True proves anything
def tlb.absurd_ft(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : tlb.IfF(_, G)
  Unit{}

def tlb.IfSome(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# a premise None == Some{x} proves anything
def tlb.none_some(-A: Data, -x: A, -G: Type, e: {None{} == Some{x} : Maybe<&2, A>}) -> G:
  %e : tlb.IfSome(A, _, G)
  Unit{}

# a premise Some{x} == None proves anything
def tlb.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  tlb.none_some(A, x, G, Equal.sym(Maybe<&2, A>, Some{x}, None{}, e))

def tlb.IfZ(n: Nat, G: Type) -> Type:
  match n:
    case 0n:
      G
    case 1n+p:
      Unit

# a premise 1 + n == 0 proves anything
def tlb.succ_zero(-n: Nat, -G: Type, e: {1n+n == 0n : Nat}) -> G:
  %e : tlb.IfZ(_, G)
  Unit{}

# Bool.not(b) is True only for b False
def tlb.not_true(b: Bool, e: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      tlb.absurd_ft({True{} == False{} : Bool}, e)
    case False{}:
      {==}

def tlb.val(-A: Data, d: A, m: Maybe<&2, A>) -> A:
  match m:
    case None{}:
      d
    case Some{x}:
      x

# Some is one to one
def tlb.some_inj(-A: Data, +x: A, +y: A, e: {Some{x} == Some{y} : Maybe<&2, A>}) -> {x == y : A}:
  Equal.cong(Maybe<&2, A>, A, m => tlb.val(A, x, m), Some{x}, Some{y}, e)

# the left side of a true and is true
def tlb.and_l(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      tlb.absurd_ft({False{} == True{} : Bool}, h)

# the right side of a true and is true
def tlb.and_r(a: Bool, -b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      tlb.absurd_ft({b == True{} : Bool}, h)

# Nat.is_eq says equal
def tlb.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      tlb.absurd_ft({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      tlb.absurd_ft({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      %tlb.eq_true(p, q, h) : {1n+p == 1n+_ : Nat}
      {==}
