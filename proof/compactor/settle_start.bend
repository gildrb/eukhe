# eukhe: the proof of LAW settle_start

import Base
import ../../bend/compactor.bend as C
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/node.bend as ONode
import ../../laws/compactor.bend as Compactor

def pc.start_step(b: Bool, +p: Nat, -m: Nat, -u: Nat, ih: {m == Nat.mul(u, 1n+p) : Nat}) -> {Nat.add(C.Pend.weight(C.settle.line(b, p)), m) == Nat.mul(Nat.add(OBits.bit(Bool.not(b), 0n), u), 1n+p) : Nat}:
  match b:
    case True{}:
      ih
    case False{}:
      %Equal.sym(Nat, m, Nat.mul(u, 1n+p), ih) : {Nat.add(1n+p, _) == Nat.add(1n+p, Nat.mul(u, 1n+p)) : Nat}
      {==}

def pc.settle_start(+p: Nat, +info: OInfo.Info, v: List<&2, ONode.Node>) -> {C.measure(C.settle.start(p, info, v)) == Nat.mul(C.unbuilt(info, v), 1n+p) : Nat}:
  match v:
    case Nil{}:
      {==}
    case +h <> +rest:
      pc.start_step(OInfo.Info.built(info, h), p, C.measure(C.settle.start(p, info, rest)), C.unbuilt(info, rest), pc.settle_start(p, info, rest))

def Compactor.settle_start(p, info, v):
  pc.settle_start(p, info, v)
