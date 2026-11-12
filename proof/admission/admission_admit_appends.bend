# eukhe: the proof of LAW admission_admit_appends
#
# PROOF: an admit appends one ticket of its class to the earlier tickets
# the model's preemption leaves (Ad.preempt.on), which are the laws'
# table (PC.pac.pre_on); its status is the model's choice, never a grant
# left to collect, and for a background request never a rejection
# (paa.ia, paa.bg).

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/admission/count.bend as PC

def paa.ia(a: Bool, b: Bool) -> {True{} == Admission.adm_fresh(Ad.Ia{}, Ad.admit.ia.st(a, b)) : Bool}:
  match a b:
    case True{} _:
      {==}
    case False{} True{}:
      {==}
    case False{} False{}:
      {==}

def paa.bg(a: Bool) -> {True{} == Admission.adm_fresh(Ad.Bg{}, Ad.admit.bg.st(a)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def paa.eq_ia(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>) -> {(Ad.step(Ad.St{l, q, ts}, Ad.Admit{Ad.Ia{}}), Admission.adm_fresh(Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))), Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts))))) == (Ad.St{l, q, List.append(&2, Ad.Tk, Admission.adm_yield(Ad.Ia{}, l, ts), [Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))), Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)))}])}, True{}) : Ad.St & Bool}:
  +a = Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)))
  +b = Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts))
  +x = Ad.admit.ia.st(a, b)
  %PC.pac.pre_on(l, ts) : {(Ad.step(Ad.St{l, q, ts}, Ad.Admit{Ad.Ia{}}), Admission.adm_fresh(Ad.Ia{}, x)) == (Ad.St{l, q, List.append(&2, Ad.Tk, _, [Ad.Tk{Ad.Ia{}, x}])}, True{}) : Ad.St & Bool}
  %paa.ia(a, b) : {(Ad.step(Ad.St{l, q, ts}, Ad.Admit{Ad.Ia{}}), _) == (Ad.St{l, q, List.append(&2, Ad.Tk, Ad.preempt.on(l, ts), [Ad.Tk{Ad.Ia{}, x}])}, True{}) : Ad.St & Bool}
  {==}

def paa.eq_bg(+l: Ad.Lim, +q: Nat, +ts: List<&2, Ad.Tk>) -> {(Ad.step(Ad.St{l, q, ts}, Ad.Admit{Ad.Bg{}}), Admission.adm_fresh(Ad.Bg{}, Ad.admit.bg.st(Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, Ad.held(ts)))))))) == (Ad.St{l, q, List.append(&2, Ad.Tk, Admission.adm_yield(Ad.Bg{}, l, ts), [Ad.Tk{Ad.Bg{}, Ad.admit.bg.st(Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, Ad.held(ts))))))}])}, True{}) : Ad.St & Bool}:
  +a = Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, Ad.held(ts)))))
  +x = Ad.admit.bg.st(a)
  %paa.bg(a) : {(Ad.step(Ad.St{l, q, ts}, Ad.Admit{Ad.Bg{}}), _) == (Ad.St{l, q, List.append(&2, Ad.Tk, ts, [Ad.Tk{Ad.Bg{}, x}])}, True{}) : Ad.St & Bool}
  {==}

def Admission.admission_admit_appends(l, q, ts, c):
  match c:
    case Ad.Ia{}:
      (Ad.admit.ia.st(Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))), Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts))), paa.eq_ia(l, q, ts))
    case Ad.Bg{}:
      (Ad.admit.bg.st(Bool.and(Ad.isz(Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, ts)), Ad.room(l, Ad.held(ts)))))), paa.eq_bg(l, q, ts))
