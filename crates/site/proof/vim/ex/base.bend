# eukhe.com's Neovim: lemmas of the Ex proofs
# ===========================================

import Base
import ../../../vim/types.bend as T
import ../../base.bend as L

# G when a key waits, Unit when none
def Pend.If(p: T.Pend, G: Type) -> Type:
  match p:
    case T.NoPend{}:
      Unit
    case T.PendG{}:
      G
    case T.PendZ{}:
      G
    case T.PendLead{}:
      G
    case T.PendLeadF{}:
      G
    case T.PendY{}:
      G

# a waiting key that is none: anything follows
def Pend.clash(-G: Type, -p: T.Pend, e: {p == T.NoPend{} : T.Pend}) -> Pend.If(p, G):
  %Equal.sym(T.Pend, p, T.NoPend{}, e) : Pend.If(_, G)
  Unit{}

# max(a, b) is a when b <= a
def Max.l(a: Nat, b: Nat, h: {Nat.is_le(b, a) == True{} : Bool}) -> {Nat.max(a, b) == a : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      L.Bool.false_true({Nat.max(0n, 1n+q) == 0n : Nat}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.max(p, q), p, Max.l(p, q, h))
