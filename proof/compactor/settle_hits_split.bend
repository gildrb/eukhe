# eukhe: the proof of LAW settle_hits_split
# Induction on a, over the view: each outcome of a adds its bit on the
# lines before it, then the rest of a and b go on from the lines after
# it; the sums regroup (associativity).

import Base
import ../../bend/compactor.bend as C
import ../../bend/optchat/bits.bend as OBits
import ../../laws/compactor.bend as Compactor
import ../base/nat.bend as LNat

def shp.go(a: List<&2, C.End>, +b: List<&2, C.End>, +ps: List<&2, C.Pend>) -> {C.hits(List.append(&2, C.End, a, b), ps) == Nat.add(C.hits(a, ps), C.hits(b, C.run(a, ps))) : Nat}:
  match a:
    case Nil{}:
      {==}
    case C.End{+k, +o} <> +rest:
      +x = OBits.bit(Bool.and(C.pending_at(ps, k), C.Outcome.lands(o)), 0n)
      +h = C.hit(ps, k, o)
      +y = C.hits(rest, h)
      +z = C.hits(b, C.run(rest, h))
      Equal.trans(Nat, Nat.add(x, C.hits(List.append(&2, C.End, rest, b), h)), Nat.add(x, Nat.add(y, z)), Nat.add(Nat.add(x, y), z),
        Equal.cong(Nat, Nat, v => Nat.add(x, v), C.hits(List.append(&2, C.End, rest, b), h), Nat.add(y, z), shp.go(rest, b, h)),
        LNat.add_assoc_r(x, y, z))

def Compactor.settle_hits_split(a, b, ps):
  shp.go(a, b, ps)
