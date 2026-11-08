# eukhe: the proof of LAW admission_step_exact
# Each op of the model is the spec's: the admits read the same counts and
# tests (admission_step_exact/count.bend), the per-ticket ops set the same
# ticket, and every grant is the spec's two passes
# (admission_step_exact/grant.bend, pag.grant).

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./admission_step_exact/count.bend as PC
import ./admission_step_exact/grant.bend as PG

def pas.admit_ia(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>) -> {Ad.admit.ia(l, q, ts) == Admission.ads_admit_ia(l, q, ts) : List<&2, Ad.Tk>}:
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
  +m = Ad.admit.ia(l, q, ts)
  %Equal.sym(Nat, Admission.ads_queued(Ad.Ia{}, ts), wi, PC.pac.queued(Ad.Ia{}, ts)) : {m == List.append(&2, Ad.Tk, Admission.ads_yield(l, ts), [Ad.Tk{Ad.Ia{}, Admission.ads_ia_status(Bool.and(Nat.is_eq(_, 0n), Admission.ads_room(l, Admission.ads_held(Ad.Ia{}, ts))), Nat.is_le(q, _))}]) : List<&2, Ad.Tk>}
  %Equal.sym(Nat, Admission.ads_held(Ad.Ia{}, ts), hi, PC.pac.held(Ad.Ia{}, ts)) : {m == List.append(&2, Ad.Tk, Admission.ads_yield(l, ts), [Ad.Tk{Ad.Ia{}, Admission.ads_ia_status(Bool.and(Nat.is_eq(wi, 0n), Admission.ads_room(l, _)), Nat.is_le(q, wi))}]) : List<&2, Ad.Tk>}
  %PC.pac.isz(wi) : {m == List.append(&2, Ad.Tk, Admission.ads_yield(l, ts), [Ad.Tk{Ad.Ia{}, Admission.ads_ia_status(Bool.and(_, Admission.ads_room(l, hi)), Nat.is_le(q, wi))}]) : List<&2, Ad.Tk>}
  %PC.pac.le(q, wi) : {m == List.append(&2, Ad.Tk, Admission.ads_yield(l, ts), [Ad.Tk{Ad.Ia{}, Admission.ads_ia_status(Bool.and(Ad.isz(wi), Admission.ads_room(l, hi)), _)}]) : List<&2, Ad.Tk>}
  %PC.pac.room(l, hi) : {m == List.append(&2, Ad.Tk, Admission.ads_yield(l, ts), [Ad.Tk{Ad.Ia{}, Admission.ads_ia_status(Bool.and(Ad.isz(wi), _), Ad.le(q, wi))}]) : List<&2, Ad.Tk>}
  %PC.pac.ia_st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi)) : {m == List.append(&2, Ad.Tk, Admission.ads_yield(l, ts), [Ad.Tk{Ad.Ia{}, _}]) : List<&2, Ad.Tk>}
  %PC.pac.pre_on(l, ts) : {m == List.append(&2, Ad.Tk, _, [Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(wi), Ad.room(l, hi)), Ad.le(q, wi))}]) : List<&2, Ad.Tk>}
  {==}

def pas.admit_bg(+l: Ad.Lim, +ts: List<&2, Ad.Tk>) -> {Ad.admit.bg(l, ts) == Admission.ads_admit_bg(l, ts) : List<&2, Ad.Tk>}:
  +hi = Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)
  +wi = Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)
  +wb = Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)
  +n = Ad.held(ts)
  +m = Ad.admit.bg(l, ts)
  %Equal.sym(Nat, Admission.ads_held(Ad.Ia{}, ts), hi, PC.pac.held(Ad.Ia{}, ts)) : {m == List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, Admission.ads_bg_status(Bool.and(Nat.is_eq(_, 0n), Bool.and(Nat.is_eq(Admission.ads_queued(Ad.Ia{}, ts), 0n), Bool.and(Nat.is_eq(Admission.ads_queued(Ad.Bg{}, ts), 0n), Admission.ads_room(l, Admission.ads_busy(ts))))))}]) : List<&2, Ad.Tk>}
  %Equal.sym(Nat, Admission.ads_queued(Ad.Ia{}, ts), wi, PC.pac.queued(Ad.Ia{}, ts)) : {m == List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, Admission.ads_bg_status(Bool.and(Nat.is_eq(hi, 0n), Bool.and(Nat.is_eq(_, 0n), Bool.and(Nat.is_eq(Admission.ads_queued(Ad.Bg{}, ts), 0n), Admission.ads_room(l, Admission.ads_busy(ts))))))}]) : List<&2, Ad.Tk>}
  %Equal.sym(Nat, Admission.ads_queued(Ad.Bg{}, ts), wb, PC.pac.queued(Ad.Bg{}, ts)) : {m == List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, Admission.ads_bg_status(Bool.and(Nat.is_eq(hi, 0n), Bool.and(Nat.is_eq(wi, 0n), Bool.and(Nat.is_eq(_, 0n), Admission.ads_room(l, Admission.ads_busy(ts))))))}]) : List<&2, Ad.Tk>}
  %Equal.sym(Nat, Admission.ads_busy(ts), n, PC.pac.busy(ts)) : {m == List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, Admission.ads_bg_status(Bool.and(Nat.is_eq(hi, 0n), Bool.and(Nat.is_eq(wi, 0n), Bool.and(Nat.is_eq(wb, 0n), Admission.ads_room(l, _)))))}]) : List<&2, Ad.Tk>}
  %PC.pac.isz(hi) : {m == List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, Admission.ads_bg_status(Bool.and(_, Bool.and(Nat.is_eq(wi, 0n), Bool.and(Nat.is_eq(wb, 0n), Admission.ads_room(l, n)))))}]) : List<&2, Ad.Tk>}
  %PC.pac.isz(wi) : {m == List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, Admission.ads_bg_status(Bool.and(Ad.isz(hi), Bool.and(_, Bool.and(Nat.is_eq(wb, 0n), Admission.ads_room(l, n)))))}]) : List<&2, Ad.Tk>}
  %PC.pac.isz(wb) : {m == List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, Admission.ads_bg_status(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(_, Admission.ads_room(l, n)))))}]) : List<&2, Ad.Tk>}
  %PC.pac.room(l, n) : {m == List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, Admission.ads_bg_status(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), _))))}]) : List<&2, Ad.Tk>}
  %PC.pac.bg_st(Bool.and(Ad.isz(hi), Bool.and(Ad.isz(wi), Bool.and(Ad.isz(wb), Ad.room(l, n))))) : {m == List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, _}]) : List<&2, Ad.Tk>}
  {==}

def pas.collect(m: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat) -> {Ad.collect.at(m, l, q, ts, k) == Admission.ads_collect(m, l, q, ts, k) : Ad.St}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      match t:
        case Ad.Tk{c, s}:
          match s:
            case Ad.Queued{}:
              {==}
            case Ad.Granted{}:
              %PC.pac.set(ts, k, Ad.Held{}) : {Ad.St{l, q, Ad.put(ts, k, Ad.Held{})} == Ad.St{l, q, _} : Ad.St}
              {==}
            case Ad.Held{}:
              {==}
            case Ad.Preempted{}:
              {==}
            case Ad.Ended{}:
              {==}

def pas.ended(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat) -> {Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))} == Ad.St{l, q, Admission.ads_grant(l, Admission.ads_set(ts, k, Ad.Ended{}))} : Ad.St}:
  %PC.pac.set(ts, k, Ad.Ended{}) : {Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))} == Ad.St{l, q, Admission.ads_grant(l, _)} : Ad.St}
  %PG.pag.grant(l, Ad.put(ts, k, Ad.Ended{})) : {Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))} == Ad.St{l, q, _} : Ad.St}
  {==}

def pas.release(m: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat) -> {Ad.release.at(m, l, q, ts, k) == Admission.ads_release(m, l, q, ts, k) : Ad.St}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      match t:
        case Ad.Tk{c, s}:
          match s:
            case Ad.Queued{}:
              {==}
            case Ad.Granted{}:
              {==}
            case Ad.Held{}:
              pas.ended(l, q, ts, k)
            case Ad.Preempted{}:
              %PC.pac.set(ts, k, Ad.Ended{}) : {Ad.St{l, q, Ad.put(ts, k, Ad.Ended{})} == Ad.St{l, q, _} : Ad.St}
              {==}
            case Ad.Ended{}:
              {==}

def pas.leave(m: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat) -> {Ad.leave.at(m, l, q, ts, k) == Admission.ads_leave(m, l, q, ts, k) : Ad.St}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      match t:
        case Ad.Tk{c, s}:
          match s:
            case Ad.Queued{}:
              pas.ended(l, q, ts, k)
            case Ad.Granted{}:
              pas.ended(l, q, ts, k)
            case Ad.Held{}:
              {==}
            case Ad.Preempted{}:
              {==}
            case Ad.Ended{}:
              {==}

def pas.step(s: Ad.St, o: Ad.Op) -> {Ad.step(s, o) == Admission.ads_step(s, o) : Ad.St}:
  match s:
    case Ad.St{+l, +q, +ts}:
      match o:
        case Ad.Admit{c}:
          match c:
            case Ad.Ia{}:
              %pas.admit_ia(l, q, ts) : {Ad.St{l, q, Ad.admit.ia(l, q, ts)} == Ad.St{l, q, _} : Ad.St}
              {==}
            case Ad.Bg{}:
              %pas.admit_bg(l, ts) : {Ad.St{l, q, Ad.admit.bg(l, ts)} == Ad.St{l, q, _} : Ad.St}
              {==}
        case Ad.Collect{+k}:
          pas.collect(List.get(&2, Ad.Tk, ts, k), l, q, ts, k)
        case Ad.Release{+k}:
          pas.release(List.get(&2, Ad.Tk, ts, k), l, q, ts, k)
        case Ad.Leave{+k}:
          pas.leave(List.get(&2, Ad.Tk, ts, k), l, q, ts, k)
        case Ad.Limit{+l2, q2}:
          %PG.pag.grant(l2, ts) : {Ad.St{l2, q2, Ad.grant(l2, ts)} == Ad.St{l2, q2, _} : Ad.St}
          {==}

def Admission.admission_step_exact(s, o):
  pas.step(s, o)
