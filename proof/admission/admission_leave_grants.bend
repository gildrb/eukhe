# eukhe: the proof of LAW admission_leave_grants
#
# PROOF: per status of ticket k: a waiter (queued or granted) is read as
# the ticket after pre (pat.got), ended in place (pat.put), and the
# model's grant loop is the two passes (pag.grant); no other status is a
# waiter.

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/at.bend as PAt
import ./base/admission/grant.bend as PG
import ./base/logic.bend as LALogic

def plg.at(+l: Ad.Lim, +q: Nat, +pre: List<&2, Ad.Tk>, +c: Ad.Cls, x: Ad.Sts, +post: List<&2, Ad.Tk>, w: {Admission.adm_waiter(x) == True{} : Bool}) -> {Ad.step(Ad.St{l, q, List.append(&2, Ad.Tk, pre, Ad.Tk{c, x} <> post)}, Ad.Leave{List.length(&2, Ad.Tk, pre)}) == Ad.St{l, q, Admission.ads_grant(l, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Ended{}} <> post))} : Ad.St}:
  match x:
    case Ad.Queued{}:
      +ts = List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Queued{}} <> post)
      +k = List.length(&2, Ad.Tk, pre)
      %PAt.pat.got(pre, Ad.Tk{c, Ad.Queued{}}, post) : {Ad.leave.at(_, l, q, ts, k) == Ad.St{l, q, Admission.ads_grant(l, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Ended{}} <> post))} : Ad.St}
      %PAt.pat.put(pre, c, Ad.Queued{}, post, Ad.Ended{}) : {Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))} == Ad.St{l, q, Admission.ads_grant(l, _)} : Ad.St}
      %PG.pag.grant(l, Ad.put(ts, k, Ad.Ended{})) : {Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))} == Ad.St{l, q, _} : Ad.St}
      {==}
    case Ad.Granted{}:
      +ts = List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Granted{}} <> post)
      +k = List.length(&2, Ad.Tk, pre)
      %PAt.pat.got(pre, Ad.Tk{c, Ad.Granted{}}, post) : {Ad.leave.at(_, l, q, ts, k) == Ad.St{l, q, Admission.ads_grant(l, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Ended{}} <> post))} : Ad.St}
      %PAt.pat.put(pre, c, Ad.Granted{}, post, Ad.Ended{}) : {Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))} == Ad.St{l, q, Admission.ads_grant(l, _)} : Ad.St}
      %PG.pag.grant(l, Ad.put(ts, k, Ad.Ended{})) : {Ad.St{l, q, Ad.grant(l, Ad.put(ts, k, Ad.Ended{}))} == Ad.St{l, q, _} : Ad.St}
      {==}
    case Ad.Held{}:
      LALogic.ad.absurd({Ad.step(Ad.St{l, q, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Held{}} <> post)}, Ad.Leave{List.length(&2, Ad.Tk, pre)}) == Ad.St{l, q, Admission.ads_grant(l, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Ended{}} <> post))} : Ad.St}, w)
    case Ad.Preempted{}:
      LALogic.ad.absurd({Ad.step(Ad.St{l, q, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Preempted{}} <> post)}, Ad.Leave{List.length(&2, Ad.Tk, pre)}) == Ad.St{l, q, Admission.ads_grant(l, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Ended{}} <> post))} : Ad.St}, w)
    case Ad.Ended{}:
      LALogic.ad.absurd({Ad.step(Ad.St{l, q, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Ended{}} <> post)}, Ad.Leave{List.length(&2, Ad.Tk, pre)}) == Ad.St{l, q, Admission.ads_grant(l, List.append(&2, Ad.Tk, pre, Ad.Tk{c, Ad.Ended{}} <> post))} : Ad.St}, w)

def Admission.admission_leave_grants(l, q, pre, c, x, post, w):
  plg.at(l, q, pre, c, x, post, w)
