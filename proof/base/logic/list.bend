# eukhe: lemmas the proofs of two or more areas share: logic/list

import Base
import ../../../bend/semver.bend as Sv
import ../../../bend/tree.bend as Tr

# the digits of q, lowest first, under the fuel g (put_nat.go's recursion)
def wn_L(g: Nat, q: Nat) -> List<&2, Nat>:
  match g:
    case 0n:
      Nil{}
    case 1n+f:
      match q:
        case 0n:
          Nil{}
        case 1n+p:
          +m = {1n+p : Nat}
          Nat.mod(m, 10n) <> wn_L(f, Nat.div(m, 10n))

# all the digits of n, lowest first
def wn_full(n: Nat) -> List<&2, Nat>:
  +m = n
  Nat.mod(m, 10n) <> wn_L(m, Nat.div(m, 10n))

def wn_Lzero(g: Nat) -> {wn_L(g, 0n) == Nil{} : List<&2, Nat>}:
  match g:
    case 0n:
      {==}
    case 1n+f:
      {==}

# Two nodes

# a and b in the order of the test lt
def tc.pair(lt: Bool, +a: Tr.Ent, +b: Tr.Ent) -> List<&2, Tr.Ent>:
  match lt:
    case True{}:
      [a, b]
    case False{}:
      [b, a]

def rk.I10(ds: List<&2, Sv.Dig>) -> List<&2, Sv.Dig>:
  Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(Sv.Num.inc(ds))))))))))

def rk.dcons(-d: Sv.Dig, -a: List<&2, Sv.Dig>, -b: List<&2, Sv.Dig>, e: {a == b : List<&2, Sv.Dig>}) -> {d <> a == d <> b : List<&2, Sv.Dig>}:
  %e : {d <> a == d <> _ : List<&2, Sv.Dig>}
  {==}
