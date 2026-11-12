# eukhe: the proof of LAW admission_background_admit_idle
#
# PROOF: the newest ticket is the one the admit appends (pat.lasted); it
# holds a slot only when the model's test holds (pbi.held), whose first
# two parts say no interactive ticket holds a slot or waits, in the
# model's counts (pbi.zero), which are the laws' (br.held, br.queued).

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/at.bend as PAt
import ./base/admission/bridge.bend as LBr
import ./base/logic.bend as LALogic

def pbi.held(a: Bool, h: {Admission.adm_took(Some{Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(a)}}) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LALogic.ad.absurd({False{} == True{} : Bool}, h)

def pbi.zero(n: Nat, e: {Ad.isz(n) == True{} : Bool}) -> {n == 0n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      LALogic.ad.absurd({1n+p == 0n : Nat}, e)

def Admission.admission_background_admit_idle(l, q, ts, took):
  +a = Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, Ad.held(ts)))))
  +h = Equal.trans(Bool, Admission.adm_took(Some{Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(a)}}), Admission.adm_took(Admission.adm_last(List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(a)}]))), True{}, Equal.cong(Maybe<&2, Ad.Tk>, Bool, m => Admission.adm_took(m), Some{Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(a)}}, Admission.adm_last(List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(a)}])), PAt.pat.lasted(ts, Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(a)})), took)
  +ea = pbi.held(a, h)
  +z1 = pbi.zero(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), LALogic.ad.and_l(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, Ad.held(ts)))), ea))
  +z2 = pbi.zero(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts), LALogic.ad.and_l(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, Ad.held(ts))), LALogic.ad.and_r(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, Ad.held(ts)))), ea)))
  %LBr.br.held(Ad.Ia{}, ts) : {(_, Admission.ads_queued(Ad.Ia{}, ts)) == (0n, 0n) : Nat & Nat}
  %LBr.br.queued(Ad.Ia{}, ts) : {(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), _) == (0n, 0n) : Nat & Nat}
  %z1 : {(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)) == (_, 0n) : Nat & Nat}
  %z2 : {(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)) == (Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts), _) : Nat & Nat}
  {==}
