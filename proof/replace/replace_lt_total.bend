# eukhe: the proof of LAW replace_lt_total
#
# PROOF of LAW replace_lt_total: by induction on both ranks (rlt.go): an
# empty rank is below every nonempty one, so neither or both are empty; of
# two nonempty ranks, two first numbers neither of which decides are equal
# (rlt.head) and leave the rest unordered both ways (rlt.tail).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ../base/logic/logic.bend as LLogicLogic

def rlt.head(x: Nat, y: Nat, -t1: Bool, -t2: Bool, a: {Rp.lex(x, y, t1) == False{} : Bool}, b: {Rp.lex(y, x, t2) == False{} : Bool}) -> {x == y : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.supervisor.ps.absurdF({0n == 1n+q : Nat}, Equal.sym(Bool, Rp.lex(0n, 1n+q, t1), False{}, a))
    case 1n+p 0n:
      LLogicLogic.supervisor.ps.absurdF({1n+p == 0n : Nat}, Equal.sym(Bool, Rp.lex(0n, 1n+p, t2), False{}, b))
    case 1n+p 1n+q:
      %rlt.head(p, q, t1, t2, a, b) : {1n+p == 1n+_ : Nat}
      {==}

def rlt.tail(x: Nat, y: Nat, -t1: Bool, -t2: Bool, a: {Rp.lex(x, y, t1) == False{} : Bool}, b: {Rp.lex(y, x, t2) == False{} : Bool}) -> {t1 == False{} : Bool}:
  match x y:
    case 0n 0n:
      a
    case 0n 1n+q:
      LLogicLogic.supervisor.ps.absurdF({t1 == False{} : Bool}, Equal.sym(Bool, Rp.lex(0n, 1n+q, t1), False{}, a))
    case 1n+p 0n:
      LLogicLogic.supervisor.ps.absurdF({t1 == False{} : Bool}, Equal.sym(Bool, Rp.lex(0n, 1n+p, t2), False{}, b))
    case 1n+p 1n+q:
      rlt.tail(p, q, t1, t2, a, b)

def rlt.go(xs: List<&2, Nat>, ys: List<&2, Nat>, +a: {Rp.lt(xs, ys) == False{} : Bool}, +b: {Rp.lt(ys, xs) == False{} : Bool}) -> {xs == ys : List<&2, Nat>}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      LLogicLogic.supervisor.ps.absurdF({Nil{} == y <> yr : List<&2, Nat>}, Equal.sym(Bool, Rp.lt(Nil{}, y <> yr), False{}, a))
    case x <> xr Nil{}:
      LLogicLogic.supervisor.ps.absurdF({x <> xr == Nil{} : List<&2, Nat>}, Equal.sym(Bool, Rp.lt(Nil{}, x <> xr), False{}, b))
    case +x <> +xr +y <> +yr:
      %rlt.head(x, y, Rp.lt(xr, yr), Rp.lt(yr, xr), a, b) : {x <> xr == _ <> yr : List<&2, Nat>}
      %rlt.go(xr, yr, rlt.tail(x, y, Rp.lt(xr, yr), Rp.lt(yr, xr), a, b), rlt.tail(y, x, Rp.lt(yr, xr), Rp.lt(xr, yr), b, a)) : {x <> xr == x <> _ : List<&2, Nat>}
      {==}

def Replace.replace_lt_total(xs, ys, no, nor):
  rlt.go(xs, ys, no, nor)
