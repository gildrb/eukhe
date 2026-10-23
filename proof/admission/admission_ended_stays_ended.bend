# eukhe: the proof of LAW admission_ended_stays_ended

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/ended.bend as LAAdmissionEnded
import ./base/logic.bend as LALogic

# Every ticket ends exactly once
# ------------------------------

# a preemption ends no ticket and revives none
def ad.end_pre1(t: Ad.Tk) -> {Ad.ended(Some{Ad.Tk.preempt(t)}) == Ad.ended(Some{t}) : Bool}:
  match t:
    case Ad.Tk{Ad.Ia{}, s}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Queued{}}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Granted{}}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Held{}}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Preempted{}}:
      {==}
    case Ad.Tk{Ad.Bg{}, Ad.Ended{}}:
      {==}

def ad.end_pre(t: List<&2, Ad.Tk>, k: Nat) -> {Ad.ended(Ad.get(Ad.preempt(t), k)) == Ad.ended(Ad.get(t, k)) : Bool}:
  match t:
    case Nil{}:
      {==}
    case +h <> +r:
      match k:
        case 0n:
          ad.end_pre1(h)
        case 1n+p:
          ad.end_pre(r, p)

def ad.end_app(t: List<&2, Ad.Tk>, -x: Ad.Tk, k: Nat, e: {Ad.ended(Ad.get(t, k)) == True{} : Bool}) -> {Ad.ended(Ad.get(List.append(&2, Ad.Tk, t, [x]), k)) == True{} : Bool}:
  match t:
    case Nil{}:
      LALogic.ad.absurd({Ad.ended(Ad.get([x], k)) == True{} : Bool}, e)
    case +h <> +r:
      match k:
        case 0n:
          e
        case 1n+p:
          ad.end_app(r, x, p, e)

# a ticket op on another ticket leaves an ended one ended
def ad.end_put(t: List<&2, Ad.Tk>, k: Nat, j: Nat, -x: Ad.Sts, e: {Ad.ended(Ad.get(t, k)) == True{} : Bool}, ne: {Ad.ended(Ad.get(t, j)) == False{} : Bool}) -> {Ad.ended(Ad.get(Ad.put(t, j, x), k)) == True{} : Bool}:
  match t:
    case Nil{}:
      e
    case Ad.Tk{+c, +s} <> +r:
      match k j:
        case 0n 0n:
          LALogic.ad.absurd({Ad.ended(Some{Ad.Tk{c, x}}) == True{} : Bool}, Equal.trans(Bool, False{}, Ad.ended(Some{Ad.Tk{c, s}}), True{}, Equal.sym(Bool, Ad.ended(Some{Ad.Tk{c, s}}), False{}, ne), e))
        case 0n 1n+q:
          e
        case 1n+p 0n:
          e
        case 1n+p 1n+q:
          ad.end_put(r, p, q, x, e, ne)

# ticket j, which is not ended, ends and the waiters are granted
def ad.ne_at(-ts: List<&2, Ad.Tk>, -j: Nat, -mb: Maybe<&2, Ad.Tk>, ej: {Ad.get(ts, j) == mb : Maybe<&2, Ad.Tk>}, f: {Ad.ended(mb) == False{} : Bool}) -> {Ad.ended(Ad.get(ts, j)) == False{} : Bool}:
  %Equal.sym(Maybe<&2, Ad.Tk>, Ad.get(ts, j), mb, ej) : {Ad.ended(_) == False{} : Bool}
  f

def ad.end_other(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, +k: Nat, +j: Nat, -c: Ad.Cls, -s: Ad.Sts, ej: {Ad.get(ts, j) == Some{Ad.Tk{c, s}} : Maybe<&2, Ad.Tk>}, ne: {Ad.ended(Some{Ad.Tk{c, s}}) == False{} : Bool}, e: {Ad.ended(Ad.get(ts, k)) == True{} : Bool}) -> {Ad.ended(Ad.get(Ad.put(ts, j, Ad.Ended{}), k)) == True{} : Bool}:
  ad.end_put(ts, k, j, Ad.Ended{}, e, ad.ne_at(ts, j, Some{Ad.Tk{c, s}}, ej, ne))

def ad.end_col(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +j: Nat, +k: Nat, ej: {Ad.get(ts, j) == mb : Maybe<&2, Ad.Tk>}, e: {Ad.ended(Ad.get(ts, k)) == True{} : Bool}) -> {Ad.ended(Ad.status(Ad.collect.at(mb, l, q, ts, j), k)) == True{} : Bool}:
  match mb:
    case None{}:
      e
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      e
    case Some{Ad.Tk{+c, Ad.Granted{}}}:
      ad.end_put(ts, k, j, Ad.Held{}, e, ad.ne_at(ts, j, Some{Ad.Tk{c, Ad.Granted{}}}, ej, {==}))
    case Some{Ad.Tk{c, Ad.Held{}}}:
      e
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      e
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      e

def ad.end_rel(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +j: Nat, +k: Nat, ej: {Ad.get(ts, j) == mb : Maybe<&2, Ad.Tk>}, e: {Ad.ended(Ad.get(ts, k)) == True{} : Bool}) -> {Ad.ended(Ad.status(Ad.release.at(mb, l, q, ts, j), k)) == True{} : Bool}:
  match mb:
    case None{}:
      e
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      e
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      e
    case Some{Ad.Tk{+c, Ad.Held{}}}:
      +t2 = Ad.put(ts, j, Ad.Ended{})
      LAAdmissionEnded.ad.end_grant_k(Ad.waits(t2), Ad.pick(l, t2), l, t2, k, ad.end_other(l, ts, k, j, c, Ad.Held{}, ej, {==}, e))
    case Some{Ad.Tk{+c, Ad.Preempted{}}}:
      ad.end_other(l, ts, k, j, c, Ad.Preempted{}, ej, {==}, e)
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      e

def ad.end_lea(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +j: Nat, +k: Nat, ej: {Ad.get(ts, j) == mb : Maybe<&2, Ad.Tk>}, e: {Ad.ended(Ad.get(ts, k)) == True{} : Bool}) -> {Ad.ended(Ad.status(Ad.leave.at(mb, l, q, ts, j), k)) == True{} : Bool}:
  match mb:
    case None{}:
      e
    case Some{Ad.Tk{+c, Ad.Queued{}}}:
      +t2 = Ad.put(ts, j, Ad.Ended{})
      LAAdmissionEnded.ad.end_grant_k(Ad.waits(t2), Ad.pick(l, t2), l, t2, k, ad.end_other(l, ts, k, j, c, Ad.Queued{}, ej, {==}, e))
    case Some{Ad.Tk{+c, Ad.Granted{}}}:
      +t2 = Ad.put(ts, j, Ad.Ended{})
      LAAdmissionEnded.ad.end_grant_k(Ad.waits(t2), Ad.pick(l, t2), l, t2, k, ad.end_other(l, ts, k, j, c, Ad.Granted{}, ej, {==}, e))
    case Some{Ad.Tk{c, Ad.Held{}}}:
      e
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      e
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      e

def ended_stays_ended(s: Ad.St, o: Ad.Op, +k: Nat, e: {Ad.ended(Ad.status(s, k)) == True{} : Bool}) -> {Ad.ended(Ad.status(Ad.step(s, o), k)) == True{} : Bool}:
  match s:
    case Ad.St{+l, +q, +ts}:
      match o:
        case Ad.Admit{Ad.Ia{}}:
          +st = Ad.admit.ia.st(Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))), Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)))
          ad.end_app(Ad.preempt(ts), Ad.Tk{Ad.Ia{}, st}, k, Equal.trans(Bool, Ad.ended(Ad.get(Ad.preempt(ts), k)), Ad.ended(Ad.get(ts, k)), True{}, ad.end_pre(ts, k), e))
        case Ad.Admit{Ad.Bg{}}:
          +st = Ad.admit.bg.st(Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, Ad.held(ts))))))
          ad.end_app(ts, Ad.Tk{Ad.Bg{}, st}, k, e)
        case Ad.Collect{+j}:
          ad.end_col(Ad.get(ts, j), l, q, ts, j, k, {==}, e)
        case Ad.Release{+j}:
          ad.end_rel(Ad.get(ts, j), l, q, ts, j, k, {==}, e)
        case Ad.Leave{+j}:
          ad.end_lea(Ad.get(ts, j), l, q, ts, j, k, {==}, e)
        case Ad.Limit{+l2, q2}:
          LAAdmissionEnded.ad.end_grant_k(Ad.waits(ts), Ad.pick(l2, ts), l2, ts, k, e)

def Admission.admission_ended_stays_ended(s, o, k, e):
  ended_stays_ended(s, o, k, e)
