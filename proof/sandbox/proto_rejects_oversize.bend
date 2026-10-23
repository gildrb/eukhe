# eukhe: the proof of LAW proto_rejects_oversize

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base.bend as LA

# b below a: a is not at most b
def px.lt_nle(a: Nat, b: Nat, h: {Nat.is_lt(b, a) == True{} : Bool}) -> {False{} == Nat.is_le(a, b) : Bool}:
  match a b:
    case 0n 0n:
      LA.px.absurdF({False{} == Nat.is_le(0n, 0n) : Bool}, h)
    case 0n 1n+q:
      LA.px.absurdF({False{} == Nat.is_le(0n, 1n+q) : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      px.lt_nle(p, q, h)

def px.proto_rejects_oversize(+i: Nat, +l: Nat, +k: Nat, +max: Nat, +allowed: List<&2, Nat>, over: {Nat.is_lt(max, l) == True{} : Bool}) -> {Sb.serve([Sb.Frame{i, l, k}], max, allowed) == Sb.Host{[Sb.Err{i}], Nil{}} : Sb.Host}:
  %px.lt_nle(l, max, over) : {Sb.host.add(Bool.and(_, Sb.elem(allowed, k)), Sb.Frame{i, l, k}, Sb.Host{Nil{}, Nil{}}) == Sb.Host{[Sb.Err{i}], Nil{}} : Sb.Host}
  {==}

def Sandbox.proto_rejects_oversize(i, l, k, max, allowed, over):
  px.proto_rejects_oversize(i, l, k, max, allowed, over)
