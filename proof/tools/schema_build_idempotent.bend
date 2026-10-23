# eukhe: the proof of LAW schema_build_idempotent

import Base
import ../../bend/tools.bend as Tl
import ../../laws/tools.bend as Tools
import ./base.bend as LA

def pl.max0(p: Nat) -> {Nat.max(p, 0n) == Nat.max(Nat.max(p, 0n), 0n) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n+q:
      {==}

def pl.max1(v: Nat) -> {Nat.max(v, 1n) == Nat.max(Nat.max(v, 1n), 1n) : Nat}:
  match v:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.max(p, 0n), Nat.max(Nat.max(p, 0n), 0n), pl.max0(p))

def pl.schema_build_idempotent(+s: Tl.Schema) -> {Tl.build(Tl.build(s)) == Tl.build(s) : Tl.Schema}:
  match s:
    case Tl.Schema{+ps, +v}:
      +p = Tl.add_intent(Tl.elem(ps, Tl.intent()), ps)
      %Equal.sym(Bool, Tl.elem(p, Tl.intent()), True{}, LA.pl.add_has(Tl.elem(ps, Tl.intent()), ps, {==})) : {Tl.Schema{Tl.add_intent(_, p), Nat.max(Nat.max(v, 1n), 1n)} == Tl.Schema{p, Nat.max(v, 1n)} : Tl.Schema}
      %pl.max1(v) : {Tl.Schema{Tl.add_intent(True{}, p), _} == Tl.Schema{p, Nat.max(v, 1n)} : Tl.Schema}
      {==}

def Tools.schema_build_idempotent(s):
  pl.schema_build_idempotent(s)
