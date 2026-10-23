# eukhe: lemmas the proofs of area admission share: admission/collect

import Base
import ../../../../bend/admission.bend as Ad
import ./cnt.bend as LAAdmissionCnt
import ../logic.bend as LALogic

# the ticket ops, by the ticket's status
def ad.col_ok(mb: Maybe<&2, Ad.Tk>, +l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, +e: {Ad.get(ts, k) == mb : Maybe<&2, Ad.Tk>}, h: {LALogic.ad.ok(l, ts) == True{} : Bool}) -> {LALogic.ad.okS(Ad.collect.at(mb, l, q, ts, k)) == True{} : Bool}:
  match mb:
    case None{}:
      h
    case Some{Ad.Tk{c, Ad.Queued{}}}:
      h
    case Some{Ad.Tk{+c, Ad.Granted{}}}:
      +t2 = Ad.put(ts, k, Ad.Held{})
      LALogic.ad.ok.tr(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Ia{}, t2), Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), LAAdmissionCnt.ad.col_cnt(Ad.Holding{}, Ad.Ia{}, ts, k, c, e)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), LAAdmissionCnt.ad.col_cnt(Ad.Waiting{}, Ad.Ia{}, ts, k, c, e)), Equal.sym(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, t2), Ad.cnt(Ad.Holding{}, Ad.Bg{}, ts), LAAdmissionCnt.ad.col_cnt(Ad.Holding{}, Ad.Bg{}, ts, k, c, e)), Equal.sym(Nat, Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t2), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts), LAAdmissionCnt.ad.col_cnt(Ad.Waiting{}, Ad.Bg{}, ts, k, c, e)), h)
    case Some{Ad.Tk{c, Ad.Held{}}}:
      h
    case Some{Ad.Tk{c, Ad.Preempted{}}}:
      h
    case Some{Ad.Tk{c, Ad.Ended{}}}:
      h
