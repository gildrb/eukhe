# eukhe: the proof of LAW force_retry_flag

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer
import ./base.bend as LA

def pi.nxx(f: Bool) -> {True{} == Bool.not(Bool.xor(f, f)) : Bool}:
  match f:
    case True{}:
      {==}
    case False{}:
      {==}

# every try of a retry carries the provider's support
def pi.flags_sup(+replies: List<&2, Bool>, +r: Nat, +f: Bool) -> {If.flags(Pair.fst(List<&2, If.Try>, If.Forced, If.force.go(replies, r, f, f)), f) == True{} : Bool}:
  match replies:
    case Nil{}:
      %pi.nxx(f) : {Bool.and(_, True{}) == True{} : Bool}
      {==}
    case c <> rest:
      match c:
        case True{}:
          match r:
            case 0n:
              %pi.nxx(f) : {Bool.and(_, True{}) == True{} : Bool}
              {==}
            case 1n+q:
              %pi.nxx(f) : {Bool.and(_, True{}) == True{} : Bool}
              {==}
        case False{}:
          match r:
            case 0n:
              %pi.nxx(f) : {Bool.and(_, True{}) == True{} : Bool}
              {==}
            case 1n+q:
              -F = Pair.fst(List<&2, If.Try>, If.Forced, If.force.go(rest, q, f, f))
              %LA.pi.fst_next(If.Try{f}, If.force.go(rest, q, f, f)) : {If.flags(_, f) == True{} : Bool}
              %pi.nxx(f) : {Bool.and(_, If.flags(F, f)) == True{} : Bool}
              pi.flags_sup(rest, q, f)

def pi.drop0(xs: List<&2, If.Try>) -> {xs == List.drop(&2, If.Try, xs, 0n) : List<&2, If.Try>}:
  match xs:
    case Nil{}:
      {==}
    case h <> t:
      {==}

def pi.retry_go(+replies: List<&2, Bool>, +r: Nat, +flag: Bool, +sup: Bool) -> {If.flags(List.drop(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force.go(replies, r, flag, sup)), 1n), sup) == True{} : Bool}:
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
              %LA.pi.fst_next(If.Try{flag}, If.force.go(rest, q, sup, sup)) : {If.flags(List.drop(&2, If.Try, _, 1n), sup) == True{} : Bool}
              %pi.drop0(Pair.fst(List<&2, If.Try>, If.Forced, If.force.go(rest, q, sup, sup))) : {If.flags(_, sup) == True{} : Bool}
              pi.flags_sup(rest, q, sup)

def pi.force_retry_flag(+r: Nat, +replies: List<&2, Bool>, +sup: Bool, +free: Bool) -> {If.flags(List.drop(&2, If.Try, Pair.fst(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free)), 1n), sup) == True{} : Bool}:
  pi.retry_go(replies, r, Bool.and(sup, free), sup)

def Infer.force_retry_flag(r, replies, sup, free):
  pi.force_retry_flag(r, replies, sup, free)
