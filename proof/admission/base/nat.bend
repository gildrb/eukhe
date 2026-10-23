# eukhe: lemmas the proofs of area admission share: nat

import Base

def ad.pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

def ad.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %ad.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def ad.add_succ(a: Nat, -b: Nat) -> {1n+Nat.add(a, b) == Nat.add(a, 1n+b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %ad.add_succ(p, b) : {2n+Nat.add(p, b) == 1n+_ : Nat}
      {==}

# ---- admission_live ----

# proof_admission_live: the live controller (Ad.Live in bend/admission.bend)
# against the model: on any state of the model, an op of the live
# controller on the model's live tickets gives the live tickets of the
# model's op (LAWS.bend admission_live_step). Each part of an op commutes
# with taking the live tickets (`Laws.adl_lives`): a count, a grant, a
# preemption, an admit (a ticket appended, numbered by the length), and a
# ticket found, set or dropped by its number (the numbers of the live
# tickets from the j-th on are at least j).

# Nat
# ---

def al.add_zero(a: Nat) -> {Nat.add(a, 0n) == a : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %al.add_zero(p) : {1n+Nat.add(p, 0n) == 1n+_ : Nat}
      {==}

def al.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %al.add_succ(p, b) : {1n+Nat.add(p, 1n+b) == 1n+_ : Nat}
      {==}

def al.eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      al.eq_refl(p)

# j is not a number past it
def al.ne_add(+i: Nat, j: Nat) -> {Nat.is_eq(j, 1n+Nat.add(i, j)) == False{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(i, 1n+p), 1n+Nat.add(i, p), al.add_succ(i, p)) : {Nat.is_eq(1n+p, 1n+_) == False{} : Bool}
      al.ne_add(i, p)

def al.ne_add2(+d: Nat, j: Nat) -> {Nat.is_eq(1n+Nat.add(d, j), j) == False{} : Bool}:
  match j:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(d, 1n+p), 1n+Nat.add(d, p), al.add_succ(d, p)) : {Nat.is_eq(1n+_, 1n+p) == False{} : Bool}
      al.ne_add2(d, p)
