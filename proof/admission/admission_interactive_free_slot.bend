# eukhe: the proof of LAW admission_interactive_free_slot
#
# PROOF: the newest ticket is the one the admit appends (pat.lasted),
# whose status is the model's admit.ia.st(free, full); free is the
# model's test on its counts (no interactive waiter, room for the
# interactive slots held), which are the laws' (pac.queued, pac.held,
# pac.room), so the premises make it true (pif.free) and the ticket
# holds its slot (pif.go).

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/at.bend as PAt
import ./base/admission/count.bend as PC
import ./base/logic.bend as LALogic

def pif.go(a: Bool, b: Bool, e: {a == True{} : Bool}) -> {Admission.adm_took(Some{Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(a, b)}}) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LALogic.ad.absurd({Admission.adm_took(Some{Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(False{}, b)}}) == True{} : Bool}, e)

def pif.free(+l: Ad.Lim, +ts: List<&2, Ad.Tk>, w0: {Admission.ads_queued(Ad.Ia{}, ts) == 0n : Nat}, fr: {Admission.ads_room(l, Admission.ads_held(Ad.Ia{}, ts)) == True{} : Bool}) -> {Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))) == True{} : Bool}:
  %PC.pac.queued(Ad.Ia{}, ts) : {Bool.and(Ad.isz(_), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))) == True{} : Bool}
  %Equal.sym(Nat, Admission.ads_queued(Ad.Ia{}, ts), 0n, w0) : {Bool.and(Ad.isz(_), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))) == True{} : Bool}
  %PC.pac.held(Ad.Ia{}, ts) : {Bool.and(Ad.isz(0n), Ad.room(l, _)) == True{} : Bool}
  %Equal.sym(Bool, Ad.room(l, Admission.ads_held(Ad.Ia{}, ts)), Admission.ads_room(l, Admission.ads_held(Ad.Ia{}, ts)), PC.pac.room(l, Admission.ads_held(Ad.Ia{}, ts))) : {Bool.and(Ad.isz(0n), _) == True{} : Bool}
  fr

def Admission.admission_interactive_free_slot(l, q, ts, w0, fr):
  +a = Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)))
  +b = Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts))
  %PAt.pat.lasted(Ad.preempt.on(l, ts), Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(a, b)}) : {Admission.adm_took(_) == True{} : Bool}
  pif.go(a, b, pif.free(l, ts, w0, fr))
