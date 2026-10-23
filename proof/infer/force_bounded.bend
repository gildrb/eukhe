# eukhe: the proof of LAW force_bounded

import Base
import ../../bend/infer.bend as If
import ../../LAWS.bend as Laws
import ../base.bend as L
import ./base.bend as LA

def pi.bounded_go(+replies: List<&2, Bool>, +r: Nat, +flag: Bool, +sup: Bool) -> {Nat.is_le(List.length(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force.go(replies, r, flag, sup))), 1n+r) == True{} : Bool}:
  match replies:
    case Nil{}:
      L.pi.le0(r)
    case c <> rest:
      match c:
        case True{}:
          match r:
            case 0n:
              {==}
            case 1n+q:
              {==}
        case False{}:
          match r:
            case 0n:
              {==}
            case 1n+q:
              %LA.pi.fst_next(If.Try{flag}, If.force.go(rest, q, sup, sup)) : {Nat.is_le(List.length(&2, If.Try, _), 2n+q) == True{} : Bool}
              pi.bounded_go(rest, q, sup, sup)

def pi.force_bounded(+r: Nat, +replies: List<&2, Bool>, +sup: Bool, +free: Bool) -> {Nat.is_le(List.length(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free))), 1n+r) == True{} : Bool}:
  pi.bounded_go(replies, r, Bool.and(sup, free), sup)

def Laws.force_bounded(r, replies, sup, free):
  pi.force_bounded(r, replies, sup, free)
