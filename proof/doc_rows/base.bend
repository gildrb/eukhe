# eukhe: lemmas the proofs of area doc_rows share

import Base

# Nat
# ---

# zero added on the right changes nothing
def drb.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 0n), p, drb.add_zero(p)) : {1n+_ == 1n+p : Nat}
      {==}

# a successor on the right comes out
def drb.add_succ(a: Nat, +b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.add(p, 1n+b), 1n+Nat.add(p, b), drb.add_succ(p, b)) : {1n+_ == 1n+1n+Nat.add(p, b) : Nat}
      {==}

# one added on the right is the successor
def drb.add_one(+n: Nat) -> {Nat.add(n, 1n) == 1n+n : Nat}:
  %Equal.sym(Nat, Nat.add(n, 1n), 1n+Nat.add(n, 0n), drb.add_succ(n, 0n)) : {_ == 1n+n : Nat}
  %Equal.sym(Nat, Nat.add(n, 0n), n, drb.add_zero(n)) : {1n+_ == 1n+n : Nat}
  {==}

# zero taken away changes nothing
def drb.sub_zero(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a successor goes through a pick
def drb.succ_pick(c: Bool, +x: Nat, +y: Nat) -> {1n+Bool.pick(Nat, c, x, y) == Bool.pick(Nat, c, 1n+x, 1n+y) : Nat}:
  match c:
    case True{}:
      {==}
    case False{}:
      {==}

# the minimum is the pick of the smaller
def drb.min_pick(+a: Nat, +b: Nat) -> {Nat.min(a, b) == Bool.pick(Nat, Nat.is_le(a, b), a, b) : Nat}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case 1n+p:
      match b:
        case 0n:
          {==}
        case 1n+q:
          %Equal.sym(Nat, Nat.min(p, q), Bool.pick(Nat, Nat.is_le(p, q), p, q), drb.min_pick(p, q)) : {1n+_ == Bool.pick(Nat, Nat.is_le(p, q), 1n+p, 1n+q) : Nat}
          drb.succ_pick(Nat.is_le(p, q), p, q)

# the minimum of a number and itself is the number
def drb.min_self(n: Nat) -> {Nat.min(n, n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %Equal.sym(Nat, Nat.min(p, p), p, drb.min_self(p)) : {1n+_ == 1n+p : Nat}
      {==}

# t is below r + 1 exactly when r is not below t
def drb.lt_flip(r: Nat, t: Nat) -> {Nat.is_lt(t, 1n+r) == Bool.not(Nat.is_lt(r, t)) : Bool}:
  match r:
    case 0n:
      match t:
        case 0n:
          {==}
        case 1n+u:
          match u:
            case 0n:
              {==}
            case 1n+v:
              {==}
    case 1n+q:
      match t:
        case 0n:
          {==}
        case 1n+u:
          drb.lt_flip(q, u)
