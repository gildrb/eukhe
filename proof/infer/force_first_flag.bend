# eukhe: the proof of LAW force_first_flag

import Base
import ../../bend/infer.bend as If
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pi.first_go(+replies: List<&2, Bool>, +r: Nat, +flag: Bool, +sup: Bool) -> {List.head(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force.go(replies, r, flag, sup))) == Some{If.Try{flag}} : Maybe<&2, If.Try>}:
  match replies:
    case Nil{}:
      {==}
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
              %LA.pi.fst_next(If.Try{flag}, If.force.go(rest, q, sup, sup)) : {List.head(&2, If.Try, _) == Some{If.Try{flag}} : Maybe<&2, If.Try>}
              {==}

def pi.force_first_flag(+r: Nat, +replies: List<&2, Bool>, +sup: Bool, +free: Bool) -> {List.head(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free))) == Some{If.Try{Bool.and(sup, free)}} : Maybe<&2, If.Try>}:
  pi.first_go(replies, r, Bool.and(sup, free), sup)

def Laws.force_first_flag(r, replies, sup, free):
  pi.force_first_flag(r, replies, sup, free)
