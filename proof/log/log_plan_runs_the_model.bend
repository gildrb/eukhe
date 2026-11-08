# eukhe: the proof of LAW log_plan_runs_the_model
#
# The plan of a commit that touches no sidecar file is append, flush,
# (the first one: directory flush), ack: the plan of the commits after the
# first does what Lg.more does (pl.plan_more), the plan of the first what
# Lg.first does (pl.plan_first), each step by step on any storage; the
# open's plan is the parent's flush, the first step of Lg.run.

import Base
import ../../spec/durable/log.bend as Lg
import ../../bend/log.bend as Lr
import ../../laws/log.bend as Log

def pl.plan_more(cs: List<&2, List<&2, Nat>>, +p: Nat, s: Lg.St) -> {Log.log_exec(Log.log_plan(cs, Lr.Store{True{}, True{}}), p, s) == Lg.more(cs, p, s) : Lg.St}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      match p:
        case 0n:
          {==}
        case 1n+p1:
          match p1:
            case 0n:
              {==}
            case 1n+p2:
              pl.plan_more(rest, p2, Lg.ack(c, Lg.flush(Lg.append(c, s))))

def pl.plan_first(cs: List<&2, List<&2, Nat>>, +q: Nat, s: Lg.St) -> {Log.log_exec(Log.log_plan(cs, Lr.Store{True{}, False{}}), q, s) == Lg.first(cs, q, s) : Lg.St}:
  match cs:
    case Nil{}:
      {==}
    case +c <> rest:
      match q:
        case 0n:
          {==}
        case 1n+q1:
          match q1:
            case 0n:
              {==}
            case 1n+q2:
              match q2:
                case 0n:
                  {==}
                case 1n+q3:
                  pl.plan_more(rest, q3, Lg.ack(c, Lg.dir(Lg.flush(Lg.append(c, s)))))

def Log.log_plan_runs_the_model(d, cs, p):
  match p:
    case 0n:
      {==}
    case 1n+q:
      pl.plan_first(cs, q, Lg.parent(Lg.open(d)))
