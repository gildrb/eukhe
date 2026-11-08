# eukhe: the proof of LAW admission_preempts

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/cnt.bend as LAAdmissionCnt
import ./base/admission/hit.bend as LAAdmissionHit
import ./base/bool.bend as LABool

# Laws (a)-(c)
# ------------

def preempts(+p: Nat, +q: Nat, +ts: List<&2, Ad.Tk>) -> {Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.St.ts(Ad.step(Ad.St{Ad.Cap{p}, q, ts}, Ad.Admit{Ad.Ia{}}))) == 0n : Nat}:
  +st = Ad.admit.ia.st(Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(Ad.Cap{p}, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))), Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)))
  +t1 = Ad.preempt(ts)
  Equal.trans(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, List.append(&2, Ad.Tk, t1, [Ad.Tk{Ad.Ia{}, st}])), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t1), 0n, LAAdmissionCnt.ad.app_off(Ad.Holding{}, Ad.Bg{}, t1, Ad.Tk{Ad.Ia{}, st}, LABool.ad.and_f(Ad.Mode.of(Ad.Holding{}, st))), LAAdmissionHit.ad.pre_hb(ts))

# (H3) A user's request never waits behind background work

def Admission.admission_preempts(p, q, ts):
  preempts(p, q, ts)
