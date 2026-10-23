# eukhe: the proof of LAW admission_end_twice_changes_nothing

import Base
import ../../bend/admission.bend as Ad
import ../../LAWS.bend as Laws
import ./base.bend as LA

# ending an ended ticket again changes nothing
def ad.twice(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, e: {Ad.ended(mb) == True{} : Bool}) -> {Ad.step(Ad.St{l, q, ts}, Ad.finish(mb, k)) == Ad.St{l, q, ts} : Ad.St}:
  match mb:
    case None{}:
      LA.ad.absurd({Ad.step(Ad.St{l, q, ts}, Ad.Release{k}) == Ad.St{l, q, ts} : Ad.St}, e)
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      LA.ad.absurd({Ad.step(Ad.St{l, q, ts}, Ad.Leave{k}) == Ad.St{l, q, ts} : Ad.St}, e)
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      LA.ad.absurd({Ad.step(Ad.St{l, q, ts}, Ad.Leave{k}) == Ad.St{l, q, ts} : Ad.St}, e)
    case Some{Ad.Tk{c, Ad.Held{}}}:
      LA.ad.absurd({Ad.step(Ad.St{l, q, ts}, Ad.Release{k}) == Ad.St{l, q, ts} : Ad.St}, e)
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      LA.ad.absurd({Ad.step(Ad.St{l, q, ts}, Ad.Release{k}) == Ad.St{l, q, ts} : Ad.St}, e)
    case Some{Ad.Tk{+c, Ad.Ended{}}}:
      %Equal.sym(Maybe<&2, Ad.Tk>, Ad.get(ts, k), Some{Ad.Tk{c, Ad.Ended{}}}, ej) : {Ad.release.at(_, l, q, ts, k) == Ad.St{l, q, ts} : Ad.St}
      {==}

def end_twice_changes_nothing(s: Ad.St, +k: Nat, e: {Ad.ended(Ad.status(s, k)) == True{} : Bool}) -> {Ad.step(s, Ad.finish(Ad.status(s, k), k)) == s : Ad.St}:
  match s:
    case Ad.St{+l, +q, +ts}:
      ad.twice(Ad.get(ts, k), l, q, ts, k, {==}, e)

def Laws.admission_end_twice_changes_nothing(s, k, e):
  end_twice_changes_nothing(s, k, e)
