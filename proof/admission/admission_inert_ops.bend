# eukhe: the proof of LAW admission_inert_ops
#
# PROOF: per op: an admit and new limits always apply; a poll, release
# or leave of a ticket it does not apply to (or of no ticket) takes the
# arm of the model that keeps the state (pio.col, pio.rel, pio.lea).

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/logic.bend as LALogic

def pio.col(m: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, no: {Admission.adm_granted.at(m) == False{} : Bool}) -> {Ad.collect.at(m, l, q, ts, k) == Ad.St{l, q, ts} : Ad.St}:
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
              LALogic.ad.absurd_t({Ad.collect.at(Some{Ad.Tk{c, Ad.Granted{}}}, l, q, ts, k) == Ad.St{l, q, ts} : Ad.St}, no)
            case Ad.Held{}:
              {==}
            case Ad.Preempted{}:
              {==}
            case Ad.Ended{}:
              {==}

def pio.rel(m: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, no: {Admission.adm_permit.at(m) == False{} : Bool}) -> {Ad.release.at(m, l, q, ts, k) == Ad.St{l, q, ts} : Ad.St}:
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
              LALogic.ad.absurd_t({Ad.release.at(Some{Ad.Tk{c, Ad.Held{}}}, l, q, ts, k) == Ad.St{l, q, ts} : Ad.St}, no)
            case Ad.Preempted{}:
              LALogic.ad.absurd_t({Ad.release.at(Some{Ad.Tk{c, Ad.Preempted{}}}, l, q, ts, k) == Ad.St{l, q, ts} : Ad.St}, no)
            case Ad.Ended{}:
              {==}

def pio.lea(m: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, no: {Admission.adm_waiter.at(m) == False{} : Bool}) -> {Ad.leave.at(m, l, q, ts, k) == Ad.St{l, q, ts} : Ad.St}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      match t:
        case Ad.Tk{c, s}:
          match s:
            case Ad.Queued{}:
              LALogic.ad.absurd_t({Ad.leave.at(Some{Ad.Tk{c, Ad.Queued{}}}, l, q, ts, k) == Ad.St{l, q, ts} : Ad.St}, no)
            case Ad.Granted{}:
              LALogic.ad.absurd_t({Ad.leave.at(Some{Ad.Tk{c, Ad.Granted{}}}, l, q, ts, k) == Ad.St{l, q, ts} : Ad.St}, no)
            case Ad.Held{}:
              {==}
            case Ad.Preempted{}:
              {==}
            case Ad.Ended{}:
              {==}

def pio.main(s: Ad.St, o: Ad.Op, no: {Admission.adm_applies(Admission.adm_ts(s), o) == False{} : Bool}) -> {Ad.step(s, o) == s : Ad.St}:
  match s:
    case Ad.St{+l, +q, +ts}:
      match o:
        case Ad.Admit{c}:
          LALogic.ad.absurd_t({Ad.step(Ad.St{l, q, ts}, Ad.Admit{c}) == Ad.St{l, q, ts} : Ad.St}, no)
        case Ad.Collect{+k}:
          pio.col(Ad.get(ts, k), l, q, ts, k, no)
        case Ad.Release{+k}:
          pio.rel(Ad.get(ts, k), l, q, ts, k, no)
        case Ad.Depart{+k}:
          pio.lea(Ad.get(ts, k), l, q, ts, k, no)
        case Ad.Limit{l2, q2}:
          LALogic.ad.absurd_t({Ad.step(Ad.St{l, q, ts}, Ad.Limit{l2, q2}) == Ad.St{l, q, ts} : Ad.St}, no)

def Admission.admission_inert_ops(s, o, no):
  pio.main(s, o, no)
