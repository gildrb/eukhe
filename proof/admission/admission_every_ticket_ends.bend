# eukhe: the proof of LAW admission_every_ticket_ends

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/misc.bend as LAAdmissionMisc
import ./base/bool.bend as LABool

# ending a ticket ends it
def ad.end_self(t: List<&2, Ad.Tk>, k: Nat, live: {Maybe.is_some(&2, Ad.Tk, Ad.get(t, k)) == True{} : Bool}) -> {Ad.ended(Ad.get(Ad.put(t, k, Ad.Ended{}), k)) == True{} : Bool}:
  match t:
    case Nil{}:
      LABool.ad.absurd({Ad.ended(None{}) == True{} : Bool}, live)
    case Ad.Tk{c, s} <> +r:
      match k:
        case 0n:
          {==}
        case 1n+p:
          ad.end_self(r, p, live)

def ad.some_at(-ts: List<&2, Ad.Tk>, -k: Nat, -mb: Maybe<&2, Ad.Tk>, ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, f: {Maybe.is_some(&2, Ad.Tk, mb) == True{} : Bool}) -> {Maybe.is_some(&2, Ad.Tk, Ad.get(ts, k)) == True{} : Bool}:
  %Equal.sym(Maybe<&2, Ad.Tk>, Ad.get(ts, k), mb, ej) : {Maybe.is_some(&2, Ad.Tk, _) == True{} : Bool}
  f

def ad.ends(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +ej: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, live: {Maybe.is_some(&2, Ad.Tk, mb) == True{} : Bool}) -> {Ad.ended(Ad.status(Ad.step(Ad.St{l, q, ts}, Ad.finish(mb, k)), k)) == True{} : Bool}:
  match mb:
    case None{}:
      LABool.ad.absurd({Ad.ended(Ad.status(Ad.step(Ad.St{l, q, ts}, Ad.Release{k}), k)) == True{} : Bool}, live)
    case Some{Ad.Tk{+c, Ad.Queued{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Maybe<&2, Ad.Tk>, Ad.get(ts, k), Some{Ad.Tk{c, Ad.Queued{}}}, ej) : {Ad.ended(Ad.get(Ad.St.ts(Ad.leave.at(_, l, q, ts, k)), k)) == True{} : Bool}
      LAAdmissionMisc.ad.end_grant_k(Ad.waits(t2), Ad.pick(l, t2), l, t2, k, ad.end_self(ts, k, ad.some_at(ts, k, Some{Ad.Tk{c, Ad.Queued{}}}, ej, {==})))
    case Some{Ad.Tk{+c, Ad.Granted{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Maybe<&2, Ad.Tk>, Ad.get(ts, k), Some{Ad.Tk{c, Ad.Granted{}}}, ej) : {Ad.ended(Ad.get(Ad.St.ts(Ad.leave.at(_, l, q, ts, k)), k)) == True{} : Bool}
      LAAdmissionMisc.ad.end_grant_k(Ad.waits(t2), Ad.pick(l, t2), l, t2, k, ad.end_self(ts, k, ad.some_at(ts, k, Some{Ad.Tk{c, Ad.Granted{}}}, ej, {==})))
    case Some{Ad.Tk{+c, Ad.Held{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      %Equal.sym(Maybe<&2, Ad.Tk>, Ad.get(ts, k), Some{Ad.Tk{c, Ad.Held{}}}, ej) : {Ad.ended(Ad.get(Ad.St.ts(Ad.release.at(_, l, q, ts, k)), k)) == True{} : Bool}
      LAAdmissionMisc.ad.end_grant_k(Ad.waits(t2), Ad.pick(l, t2), l, t2, k, ad.end_self(ts, k, ad.some_at(ts, k, Some{Ad.Tk{c, Ad.Held{}}}, ej, {==})))
    case Some{Ad.Tk{+c, Ad.Preempted{}}}:
      %Equal.sym(Maybe<&2, Ad.Tk>, Ad.get(ts, k), Some{Ad.Tk{c, Ad.Preempted{}}}, ej) : {Ad.ended(Ad.get(Ad.St.ts(Ad.release.at(_, l, q, ts, k)), k)) == True{} : Bool}
      ad.end_self(ts, k, ad.some_at(ts, k, Some{Ad.Tk{c, Ad.Preempted{}}}, ej, {==}))
    case Some{Ad.Tk{+c, Ad.Ended{}}}:
      %Equal.sym(Maybe<&2, Ad.Tk>, Ad.get(ts, k), Some{Ad.Tk{c, Ad.Ended{}}}, ej) : {Ad.ended(Ad.get(Ad.St.ts(Ad.release.at(_, l, q, ts, k)), k)) == True{} : Bool}
      %Equal.sym(Maybe<&2, Ad.Tk>, Ad.get(ts, k), Some{Ad.Tk{c, Ad.Ended{}}}, ej) : {Ad.ended(_) == True{} : Bool}
      {==}

def every_ticket_ends(s: Ad.St, +k: Nat, live: {Maybe.is_some(&2, Ad.Tk, Ad.status(s, k)) == True{} : Bool}) -> {Ad.ended(Ad.status(Ad.step(s, Ad.finish(Ad.status(s, k), k)), k)) == True{} : Bool}:
  match s:
    case Ad.St{+l, +q, +ts}:
      ad.ends(Ad.get(ts, k), l, q, ts, k, {==}, live)

def Admission.admission_every_ticket_ends(s, k, live):
  every_ticket_ends(s, k, live)
