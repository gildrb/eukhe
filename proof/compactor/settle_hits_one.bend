# eukhe: the proof of LAW settle_hits_one
# One outcome adds its bit to no more outcomes (0); the bit is 1 exactly
# when line k is there, owed, and the call saved its line or failed
# (shs.bit, by induction on the view and k).

import Base
import ../../bend/compactor.bend as C
import ../../bend/optchat/bits.bend as OBits
import ../../laws/compactor.bend as Compactor
import ./base.bend as LA

def shs.bit(ps: List<&2, C.Pend>, k: Nat, o: C.Outcome) -> {OBits.bit(Bool.and(C.pending_at(ps, k), C.Outcome.lands(o)), 0n) == Compactor.counts(List.get(&2, C.Pend, ps, k), o) : Nat}:
  match ps k:
    case Nil{} j:
      {==}
    case C.Made{} <> rest 0n:
      {==}
    case C.Owed{n} <> rest 0n:
      match o:
        case C.Built{}:
          {==}
        case C.Failed{}:
          {==}
        case C.Disk{}:
          {==}
        case C.Stopped{}:
          {==}
    case p <> rest 1n+j:
      shs.bit(rest, j, o)

def Compactor.settle_hits_one(ps, k, o):
  +x = OBits.bit(Bool.and(C.pending_at(ps, k), C.Outcome.lands(o)), 0n)
  Equal.trans(Nat, Nat.add(x, 0n), x, Compactor.counts(List.get(&2, C.Pend, ps, k), o), LA.lp.add_zero(x), shs.bit(ps, k, o))
