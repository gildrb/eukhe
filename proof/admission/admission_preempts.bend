# eukhe: the proof of LAW admission_preempts

import Base
import ../../bend/admission.bend as Ad
import ../../LAWS.bend as Laws
import ./base.bend as LA

# Laws (a)-(c)
# ------------

def preempts(s: Ad.St) -> {Ad.cnt(Ad.Holding{}, Ad.Bg{}, Ad.St.ts(Ad.step(s, Ad.Admit{Ad.Ia{}}))) == 0n : Nat}:
  match s:
    case Ad.St{+l, +q, +ts}:
      +st = Ad.admit.ia.st(Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(l, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))), Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)))
      +t1 = Ad.preempt(ts)
      Equal.trans(Nat, Ad.cnt(Ad.Holding{}, Ad.Bg{}, List.append(&2, Ad.Tk, t1, [Ad.Tk{Ad.Ia{}, st}])), Ad.cnt(Ad.Holding{}, Ad.Bg{}, t1), 0n, LA.ad.app_off(Ad.Holding{}, Ad.Bg{}, t1, Ad.Tk{Ad.Ia{}, st}, LA.ad.and_f(Ad.Mode.of(Ad.Holding{}, st))), LA.ad.pre_hb(ts))

# (H3) A user's request never waits behind background work

def Laws.admission_preempts(s):
  preempts(s)
