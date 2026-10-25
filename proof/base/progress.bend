# eukhe: lemmas the proofs of two or more areas share: progress

import Base
import ../../bend/progress.bend as Pr

# adding an act the ledger does not hold puts it in front
def pp.add_new(+s: List<&2, Nat>, +x: Nat, m: {Pr.mem(x, s) == False{} : Bool}) -> {Pr.add(s, x) == x <> s : List<&2, Nat>}:
  %Equal.sym(Bool, Pr.mem(x, s), False{}, m) : {Pr.add.put(_, x, s) == x <> s : List<&2, Nat>}
  {==}

def pw.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

# a claim that Some is None proves anything
def pw.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : pw.if_none(A, _, G)
  Unit{}
