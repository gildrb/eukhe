# eukhe: lemmas the proofs of area cron share: maybe

import Base

def cron.pc.MD(m: Maybe<&2, Nat>, A: Type) -> Type:
  match m:
    case None{}:
      A
    case Some{x}:
      Unit

def pc.some_none(-A: Type, -x: Nat, e: {Some{x} == None{} : Maybe<&2, Nat>}) -> A:
  %e : cron.pc.MD(_, A)
  Unit{}
