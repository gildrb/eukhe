# eukhe: the proof of LAW proto_oks_adds
#
# PROOF: by induction on the first list: each frame adds its count in
# front of the rest's (poa.go), regrouped by the sum's associativity.

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base.bend as LA
import ../base/nat.bend as LNat

def poa.go(a: List<&2, Sb.Frame>, +b: List<&2, Sb.Frame>, +max: Nat, +allowed: List<&2, Nat>) -> {Sb.oks(List.append(&2, Sb.Frame, a, b), max, allowed) == Nat.add(Sb.oks(a, max, allowed), Sb.oks(b, max, allowed)) : Nat}:
  match a:
    case Nil{}:
      {==}
    case +f <> +rest:
      +n = Sb.one(Sb.accepts(max, allowed, f))
      %Equal.sym(Nat, Sb.oks(List.append(&2, Sb.Frame, rest, b), max, allowed), Nat.add(Sb.oks(rest, max, allowed), Sb.oks(b, max, allowed)), poa.go(rest, b, max, allowed)) : {Nat.add(n, _) == Nat.add(Nat.add(n, Sb.oks(rest, max, allowed)), Sb.oks(b, max, allowed)) : Nat}
      Equal.sym(Nat, Nat.add(Nat.add(n, Sb.oks(rest, max, allowed)), Sb.oks(b, max, allowed)), Nat.add(n, Nat.add(Sb.oks(rest, max, allowed), Sb.oks(b, max, allowed))), LNat.add_assoc(n, Sb.oks(rest, max, allowed), Sb.oks(b, max, allowed)))

def Sandbox.proto_oks_adds(a, b, max, allowed):
  poa.go(a, b, max, allowed)
