# eukhe: the proof of LAW proto_oks_one
#
# PROOF: by cases on the frame's acceptance (poo.go), then evaluation.

import Base
import ../../bend/sandbox.bend as Sb
import ../../laws/sandbox.bend as Sandbox
import ./base.bend as LA

def poo.go(t: Bool) -> {Nat.add(Sb.one(t), 0n) == Bool.pick(Nat, t, 1n, 0n) : Nat}:
  match t:
    case True{}:
      {==}
    case False{}:
      {==}

def Sandbox.proto_oks_one(f, max, allowed):
  poo.go(Sb.accepts(max, allowed, f))
