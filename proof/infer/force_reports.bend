# eukhe: the proof of LAW force_reports

import Base
import ../../bend/infer.bend as If
import ../../laws/infer.bend as Infer

def pi.snd_next(-t: If.Try, p: List<&2, If.Try> & If.Forced) -> {Pair.snd(List<&2, If.Try>, If.Forced, p) == Pair.snd(List<&2, If.Try>, If.Forced, If.force.next(t, p)) : If.Forced}:
  (ts, o) = p
  {==}

def pi.reports_go(+replies: List<&2, Bool>, +r: Nat, +flag: Bool, +sup: Bool) -> {If.Forced.called(Pair.snd(List<&2, If.Try>, If.Forced, If.force.go(replies, r, flag, sup))) == If.called_within(1n+r, replies) : Bool}:
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
              %pi.snd_next(If.Try{flag}, If.force.go(rest, q, sup, sup)) : {If.Forced.called(_) == If.called_within(1n+q, rest) : Bool}
              pi.reports_go(rest, q, sup, sup)

def pi.force_reports(+r: Nat, +replies: List<&2, Bool>, +sup: Bool, +free: Bool) -> {If.Forced.called(Pair.snd(List<&2, If.Try>, If.Forced, If.force(r, replies, sup, free))) == If.called_within(1n+r, replies) : Bool}:
  pi.reports_go(replies, r, Bool.and(sup, free), sup)

def Infer.force_reports(r, replies, sup, free):
  pi.force_reports(r, replies, sup, free)
