# eukhe: the proof of LAW schema_versioned

import Base
import ../../bend/tools.bend as Tl
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pl.ver(v: Nat) -> {Nat.is_le(1n, Nat.max(v, 1n)) == True{} : Bool}:
  match v:
    case 0n:
      {==}
    case 1n+p:
      LA.pl.le0(Nat.max(p, 0n))

def pl.schema_versioned(s: Tl.Schema) -> {Nat.is_le(1n, Tl.Schema.version(Tl.build(s))) == True{} : Bool}:
  match s:
    case Tl.Schema{ps, v}:
      pl.ver(v)

def Laws.schema_versioned(s):
  pl.schema_versioned(s)
