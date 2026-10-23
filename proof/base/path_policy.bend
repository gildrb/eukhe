# eukhe: lemmas the proofs of two or more areas share: path_policy

import Base
import ../../bend/path_policy.bend as Pp
import ./bool/misc.bend as LBoolMisc

# A at Inside, Unit elsewhere: refutes {c == Inside} for c not Inside
def pp.CM(c: Pp.Cls, A: Type) -> Type:
  match c:
    case Pp.Inside{}:
      A
    case Pp.Outside{}:
      Unit
    case Pp.Protected{}:
      Unit
    case Pp.Secret{}:
      Unit

def pp.not_inside(-A: Type, c: Pp.Cls, n: {Pp.Cls.inside(c) == False{} : Bool}, e: {c == Pp.Inside{} : Pp.Cls}) -> A:
  match c:
    case Pp.Inside{}:
      LBoolMisc.pp.absurd(A, n)
    case Pp.Outside{}:
      %e : pp.CM(_, A)
      Unit{}
    case Pp.Protected{}:
      %e : pp.CM(_, A)
      Unit{}
    case Pp.Secret{}:
      %e : pp.CM(_, A)
      Unit{}
