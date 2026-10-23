# optchat: pair geometry and the candidate pairs: every line's built ancestors

import Base
import ./bits.bend as OBits
import ./node.bend as ONode
import ./info.bend as OInfo
import ./sizemap.bend as OSizemap

# 2i in bits, without a high zero bit
def fitx.dbl(i: List<&2, Bool>) -> List<&2, Bool>:
  match i:
    case Nil{}:
      Nil{}
    case h <> t:
      False{} <> h <> t

# the first line of the pair whose parent is p
def fitx.head(p: ONode.Node) -> ONode.Node:
  match p:
    case ONode.Node{l, i}:
      match l:
        case 0n:
          ONode.Node{0n, fitx.dbl(i)}
        case 1n+k:
          ONode.Node{k, fitx.dbl(i)}

# the pair's second line (h has low bit 0)
def fitx.second(h: ONode.Node) -> ONode.Node:
  match h:
    case ONode.Node{l, i}:
      ONode.Node{l, OBits.Bits.inc(i)}

# A pair that may merge: its first line and its parent's size.
type Cand is Data:
  Cand{h: ONode.Node, z: Nat}

# from p up: every built ancestor not seen yet
def fitx.up(fuel: Nat, got: Maybe<&2, Nat>, there: Bool, +info: OInfo.Info, +p: ONode.Node, xs: List<&2, Cand>, seen: OSizemap.Sizes) -> List<&2, Cand> & OSizemap.Sizes:
  match fuel got there:
    case 0n _ _:
      (xs, seen)
    case 1n+f None{} _:
      (xs, seen)
    case 1n+f Some{z} True{}:
      (xs, seen)
    case 1n+f Some{+z} False{}:
      +q = ONode.Node.parent(p)
      +seen2 = OSizemap.fitx.put(seen, p, z)
      fitx.up(f, OInfo.Info.get(info, q), OSizemap.fitx.has(seen2, q), info, q, Cand{fitx.head(p), z} <> xs, seen2)

def fitx.all.step(+fuel: Nat, +info: OInfo.Info, +x: ONode.Node, r: List<&2, Cand> & OSizemap.Sizes) -> List<&2, Cand> & OSizemap.Sizes:
  (xs, seen) = r
  +s = seen
  +p = ONode.Node.parent(x)
  fitx.up(fuel, OInfo.Info.get(info, p), OSizemap.fitx.has(s, p), info, p, xs, s)

def fitx.all(v: List<&2, ONode.Node>, +fuel: Nat, +info: OInfo.Info, r: List<&2, Cand> & OSizemap.Sizes) -> List<&2, Cand> & OSizemap.Sizes:
  match v:
    case Nil{}:
      r
    case x <> rest:
      fitx.all(rest, fuel, info, fitx.all.step(fuel, info, x, r))
