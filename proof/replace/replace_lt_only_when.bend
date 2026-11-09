# eukhe: the proof of LAW replace_lt_only_when
#
# PROOF of LAW replace_lt_only_when: by induction on both ranks (rlo.go).
# Nothing is below the empty rank; the empty rank is below y <> yr, which
# extends it. Of two nonempty ranks, split the compare of the first numbers
# (rlo.cmp): LT is the first difference, at the empty prefix; GT answers
# False; EQ makes the first numbers equal (rlo.eq) and the rest below,
# whose witness gains the shared number (rlo.lift).

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ../base/logic/logic.bend as LLogicLogic

# compare answers EQ only for equal numbers
def rlo.eq(x: Nat, y: Nat, e: {Nat.cmp(x, y) == EQ{} : Cmp}) -> {x == y : Nat}:
  match x y:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LLogicLogic.supervisor.ps.absurdF({0n == 1n+q : Nat}, Equal.cong(Cmp, Bool, Cmp.is_eq, LT{}, EQ{}, e))
    case 1n+p 0n:
      LLogicLogic.supervisor.ps.absurdF({1n+p == 0n : Nat}, Equal.cong(Cmp, Bool, Cmp.is_eq, GT{}, EQ{}, e))
    case 1n+p 1n+q:
      %rlo.eq(p, q, e) : {1n+p == 1n+_ : Nat}
      {==}

# compare answers LT only when x < y
def rlo.less(-x: Nat, -y: Nat, e: {Nat.cmp(x, y) == LT{} : Cmp}) -> {Nat.is_lt(x, y) == True{} : Bool}:
  %Equal.sym(Cmp, Nat.cmp(x, y), LT{}, e) : {Cmp.is_lt(_) == True{} : Bool}
  {==}

# a shared number put before both: the cons of an equal list
def rlo.cons(-x: Nat, -xr: List<&2, Nat>, -l: List<&2, Nat>, e: {xr == l : List<&2, Nat>}) -> {x <> xr == x <> l : List<&2, Nat>}:
  %e : {x <> xr == x <> _ : List<&2, Nat>}
  {==}

# y <> yr, with y equal to x, is x before a list equal to yr
def rlo.cons2(-x: Nat, -y: Nat, -yr: List<&2, Nat>, -l: List<&2, Nat>, exy: {x == y : Nat}, e: {yr == l : List<&2, Nat>}) -> {y <> yr == x <> l : List<&2, Nat>}:
  %e : {y <> yr == x <> _ : List<&2, Nat>}
  %exy : {_ <> yr == x <> yr : List<&2, Nat>}
  {==}

# a witness for the rests, the first numbers equal, is one for the ranks
def rlo.lift(+x: Nat, -y: Nat, -xr: List<&2, Nat>, -yr: List<&2, Nat>, +exy: {x == y : Nat}, r: Replace.rp_extends(xr, yr) | Replace.rp_first_smaller(xr, yr)) -> Replace.rp_extends(x <> xr, y <> yr) | Replace.rp_first_smaller(x <> xr, y <> yr):
  match r:
    case Inl{v}:
      (z, zr, e) = v
      Inl{(z, zr, rlo.cons2(x, y, yr, List.append(&2, Nat, xr, z <> zr), exy, e))}
    case Inr{v}:
      (p, a, ar, b, br, e1, e2, l) = v
      Inr{(x <> p, a, ar, b, br, rlo.cons(x, xr, List.append(&2, Nat, p, a <> ar), e1), rlo.cons2(x, y, yr, List.append(&2, Nat, p, b <> br), exy, e2), l)}

# two nonempty ranks, by the compare c of their first numbers
def rlo.cmp(c: Cmp, +x: Nat, +y: Nat, +xr: List<&2, Nat>, +yr: List<&2, Nat>, e: {Nat.cmp(x, y) == c : Cmp}, h: {Rp.lex.put(c, Rp.lt(xr, yr)) == True{} : Bool}, k: {Rp.lt(xr, yr) == True{} : Bool} -> Replace.rp_extends(xr, yr) | Replace.rp_first_smaller(xr, yr)) -> Replace.rp_extends(x <> xr, y <> yr) | Replace.rp_first_smaller(x <> xr, y <> yr):
  match c:
    case LT{}:
      Inr{(Nil{}, x, xr, y, yr, {==}, {==}, rlo.less(x, y, e))}
    case EQ{}:
      rlo.lift(x, y, xr, yr, rlo.eq(x, y, e), k(h))
    case GT{}:
      LLogicLogic.supervisor.ps.absurdF(Replace.rp_extends(x <> xr, y <> yr) | Replace.rp_first_smaller(x <> xr, y <> yr), h)

def rlo.go(xs: List<&2, Nat>, ys: List<&2, Nat>, h: {Rp.lt(xs, ys) == True{} : Bool}) -> Replace.rp_extends(xs, ys) | Replace.rp_first_smaller(xs, ys):
  match xs ys:
    case Nil{} Nil{}:
      LLogicLogic.supervisor.ps.absurdF(Replace.rp_extends(Nil{}, Nil{}) | Replace.rp_first_smaller(Nil{}, Nil{}), h)
    case Nil{} +y <> +yr:
      Inl{(y, yr, {==})}
    case x <> xr Nil{}:
      LLogicLogic.supervisor.ps.absurdF(Replace.rp_extends(x <> xr, Nil{}) | Replace.rp_first_smaller(x <> xr, Nil{}), h)
    case +x <> +xr +y <> +yr:
      rlo.cmp(Nat.cmp(x, y), x, y, xr, yr, {==}, h, a => rlo.go(xr, yr, a))

def Replace.replace_lt_only_when(xs, ys, below):
  rlo.go(xs, ys, below)
