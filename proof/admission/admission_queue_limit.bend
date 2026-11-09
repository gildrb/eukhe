# eukhe: the proof of LAW admission_queue_limit
#
# PROOF: the newest ticket is the one the admit appends (pat.lasted),
# whose status is the model's admit.ia.st(free, full) with full the
# model's test of the laws' count (br.queued, pac.le): rejected exactly
# when not free (not held) and full (pql.st).

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/at.bend as PAt
import ./base/admission/bridge.bend as LBr
import ./base/admission/count.bend as PC

def pql.st(a: Bool, b: Bool) -> {Admission.adm_ended(Some{Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(a, b)}}) == Bool.and(Bool.not(Admission.adm_took(Some{Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(a, b)}})), b) : Bool}:
  match a b:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def Admission.admission_queue_limit(l, q, ts):
  +a = Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)))
  +b = Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts))
  %PAt.pat.lasted(Ad.preempt.on(l, ts), Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(a, b)}) : {Admission.adm_ended(_) == Bool.and(Bool.not(Admission.adm_took(_)), Nat.is_le(q, Admission.ads_queued(Ad.Ia{}, ts))) : Bool}
  %LBr.br.queued(Ad.Ia{}, ts) : {Admission.adm_ended(Some{Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(a, b)}}) == Bool.and(Bool.not(Admission.adm_took(Some{Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(a, b)}})), Nat.is_le(q, _)) : Bool}
  %PC.pac.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)) : {Admission.adm_ended(Some{Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(a, b)}}) == Bool.and(Bool.not(Admission.adm_took(Some{Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(a, b)}})), _) : Bool}
  pql.st(a, b)
