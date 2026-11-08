# eukhe: the proof of LAW replace_lt_asymmetric
#
# PROOF of LAW replace_lt_asymmetric: by induction on both ranks (rla.go):
# the empty rank is below no rank; of two first numbers, the smaller one
# decides both ways, and equal ones pass the question to the rest
# (rla.lex).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ../base/logic/logic.bend as LLogicLogic

def rla.lex(x: Nat, y: Nat, -t1: Bool, -t2: Bool, h: {Rp.lex(x, y, t1) == True{} : Bool}, k: {t1 == True{} : Bool} -> {t2 == False{} : Bool}) -> {Rp.lex(y, x, t2) == False{} : Bool}:
  match x y:
    case 0n 0n:
      k(h)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LLogicLogic.supervisor.ps.absurdF({Rp.lex(0n, 1n+p, t2) == False{} : Bool}, h)
    case 1n+p 1n+q:
      rla.lex(p, q, t1, t2, h, k)

def rla.go(xs: List<&2, Nat>, ys: List<&2, Nat>, h: {Rp.lt(xs, ys) == True{} : Bool}) -> {Rp.lt(ys, xs) == False{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      {==}
    case x <> xr Nil{}:
      LLogicLogic.supervisor.ps.absurdF({Rp.lt(Nil{}, x <> xr) == False{} : Bool}, h)
    case x <> +xr y <> +yr:
      rla.lex(x, y, Rp.lt(xr, yr), Rp.lt(yr, xr), h, a => rla.go(xr, yr, a))

def Replace.replace_lt_asymmetric(xs, ys, below):
  rla.go(xs, ys, below)
