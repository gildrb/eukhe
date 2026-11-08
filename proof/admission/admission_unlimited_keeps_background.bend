# eukhe: the proof of LAW admission_unlimited_keeps_background
#
# PROOF: on an unlimited provider an interactive admit preempts nothing
# (Ad.preempt.on of Unl is the tickets as they are) and appends its own
# ticket after them, so every ticket before it reads back unchanged.

import Base
import ../../bend/admission.bend as Ad
import ../../laws/admission.bend as Admission
import ./base/logic.bend as LALogic

# a ticket appended at the end leaves every ticket before it in place
def uk.get_app(ts: List<&2, Ad.Tk>, k: Nat, -x: Ad.Tk, e: {Maybe.is_some(&2, Ad.Tk, Ad.get(ts, k)) == True{} : Bool}) -> {Ad.get(List.append(&2, Ad.Tk, ts, [x]), k) == Ad.get(ts, k) : Maybe<&2, Ad.Tk>}:
  match ts k:
    case Nil{} _:
      LALogic.ad.absurd({Ad.get([x], k) == None{} : Maybe<&2, Ad.Tk>}, e)
    case h <> t 0n:
      {==}
    case h <> t 1n+p:
      uk.get_app(t, p, x, e)

def keeps_background(q: Nat, +ts: List<&2, Ad.Tk>, +k: Nat, live: {Maybe.is_some(&2, Ad.Tk, Ad.get(ts, k)) == True{} : Bool}) -> {Ad.get(Ad.St.ts(Ad.step(Ad.St{Ad.Unl{}, q, ts}, Ad.Admit{Ad.Ia{}})), k) == Ad.get(ts, k) : Maybe<&2, Ad.Tk>}:
  uk.get_app(ts, k, Ad.Tk{Ad.Ia{}, Ad.admit.ia.st(Bool.and(Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)), Ad.room(Ad.Unl{}, Ad.cnt(Ad.Holding{}, Ad.Ia{}, ts))), Ad.le(q, Ad.cnt(Ad.Waiting{}, Ad.Ia{}, ts)))}, live)

# (H3) A user's request never waits behind background work

def Admission.admission_unlimited_keeps_background(q, ts, k, live):
  keeps_background(q, ts, k, live)
