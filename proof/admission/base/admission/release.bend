# eukhe: lemmas the proofs of area admission share: admission/release

import Base
import ../../../../bend/admission.bend as Ad
import ./bit.bend as LAAdmissionBit
import ./calm.bend as LAAdmissionCalm
import ./pick.bend as LAAdmissionPick
import ../logic.bend as LALogic

def ad.rel_ok(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, +h: {LALogic.ad.ok(l, ts) == True{} : Bool}) -> {LALogic.ad.okS(Ad.release.at(mb, l, q, ts, k)) == True{} : Bool}:
  match mb:
    case None{}:
      h
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      h
    case Some{Ad.Tk{c, Ad.Granted{}}}:
      h
    case Some{Ad.Tk{+c, Ad.Held{}}}:
      LAAdmissionPick.ad.end_grant(l, ts, k, c, Ad.Held{}, e, LAAdmissionCalm.ad.calm_of(l, ts, h))
    case Some{Ad.Tk{+c, Ad.Preempted{}}}:
      +t2 = Ad.put(ts, k, Ad.Ended{})
      LALogic.ad.ok.tr(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), LAAdmissionBit.ad.end_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, c, Ad.Preempted{}, e)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), LAAdmissionBit.ad.end_cnt(Ad.Waiting{}, Ad.Ia{}, ts, k, c, Ad.Preempted{}, e)), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), LAAdmissionBit.ad.end_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, c, Ad.Preempted{}, e)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts), LAAdmissionBit.ad.end_cnt(Ad.Waiting{}, Ad.Bg{}, ts, k, c, Ad.Preempted{}, e)), h)
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      h
