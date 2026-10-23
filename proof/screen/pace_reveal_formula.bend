# eukhe: the proof of LAW pace_reveal_formula

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen.bend as Screen
import ../base.bend as L

# The share's guard: when k >= b the quotient b / (1 + k) is 0
def ps.div_small(n: Nat, m: Nat, -r: Nat, h: {Nat.is_lt(m, n) == False{} : Bool}) -> {Pair.fst(Nat, Nat, Nat.divmod.go(n, m, 0n, r)) == 0n : Nat}:
  match n m:
    case 0n _:
      {==}
    case 1n+np 0n:
      L.screen.ps.absurdF({Pair.fst(Nat, Nat, Nat.divmod.go(1n+np, 0n, 0n, r)) == 0n : Nat}, Equal.sym(Bool, Nat.is_lt(0n, 1n+np), False{}, h))
    case 1n+np 1n+mp:
      ps.div_small(np, mp, 1n+r, h)

def ps.reveal_at(+min: Nat, +k: Nat, +b: Nat, lt: Bool, e: {Nat.is_lt(k, b) == lt : Bool}) -> {Nat.min(b, Nat.max(min, Sc.share.at(lt, k, b))) == Nat.min(b, Nat.max(min, Nat.div(b, 1n+k))) : Nat}:
  match lt:
    case True{}:
      {==}
    case False{}:
      %ps.div_small(b, k, 0n, e) : {Nat.min(b, Nat.max(min, _)) == Nat.min(b, Nat.max(min, Nat.div(b, 1n+k))) : Nat}
      {==}

def ps.pace_reveal_formula(+min: Nat, +k: Nat, +b: Nat) -> {Sc.reveal(min, k, b) == Nat.min(b, Nat.max(min, Nat.div(b, 1n+k))) : Nat}:
  ps.reveal_at(min, k, b, Nat.is_lt(k, b), {==})

def Screen.pace_reveal_formula(min, k, b):
  ps.pace_reveal_formula(min, k, b)
