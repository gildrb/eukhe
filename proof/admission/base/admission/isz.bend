# eukhe: lemmas the proofs of area admission share: admission/isz

import Base
import ../../../../bend/admission.bend as Ad
import ../logic.bend as LALogic

# a grant to an interactive waiter: one waits
def ad.pick_ia(r: Bool, wi: Nat, hi: Nat, wb: Nat, e: {Ad.pick.go(r, wi, hi, wb) == Some{Ad.Ia{}} : Maybe<&2, Ad.Cls>}) -> {Ad.isz(wi) == False{} : Bool}:
  match r wi hi wb:
    case False{} _ _ _:
      LALogic.ad.m_ia({Ad.isz(wi) == False{} : Bool}, None{}, e, Unit{})
    case True{} 1n+a _ _:
      {==}
    case True{} 0n 1n+b _:
      LALogic.ad.m_ia({Ad.isz(0n) == False{} : Bool}, None{}, e, Unit{})
    case True{} 0n 0n 0n:
      LALogic.ad.m_ia({Ad.isz(0n) == False{} : Bool}, None{}, e, Unit{})
    case True{} 0n 0n 1n+d:
      LALogic.ad.m_ia({Ad.isz(0n) == False{} : Bool}, Some{Ad.Bg{}}, e, Unit{})

# a grant to a background waiter: no interactive request holds or waits,
# and one background request waits
def ad.pick_bg(r: Bool, wi: Nat, hi: Nat, wb: Nat, e: {Ad.pick.go(r, wi, hi, wb) == Some{Ad.Bg{}} : Maybe<&2, Ad.Cls>}) -> {wi == 0n : Nat} & ({hi == 0n : Nat} & {Ad.isz(wb) == False{} : Bool}):
  match r wi hi wb:
    case False{} _ _ _:
      LALogic.ad.m_bg({wi == 0n : Nat} & ({hi == 0n : Nat} & {Ad.isz(wb) == False{} : Bool}), None{}, e, Unit{})
    case True{} 1n+a _ _:
      LALogic.ad.m_bg({1n+a == 0n : Nat} & ({hi == 0n : Nat} & {Ad.isz(wb) == False{} : Bool}), Some{Ad.Ia{}}, e, Unit{})
    case True{} 0n 1n+b _:
      LALogic.ad.m_bg({0n == 0n : Nat} & ({1n+b == 0n : Nat} & {Ad.isz(wb) == False{} : Bool}), None{}, e, Unit{})
    case True{} 0n 0n 0n:
      LALogic.ad.m_bg({0n == 0n : Nat} & ({0n == 0n : Nat} & {Ad.isz(0n) == False{} : Bool}), None{}, e, Unit{})
    case True{} 0n 0n 1n+d:
      ({==}, ({==}, {==}))

def ad.pbg(+l: Ad.Lim, +t: List<&2, Ad.Tk>, e: {Ad.pick(l, t) == Some{Ad.Bg{}} : Maybe<&2, Ad.Cls>}) -> {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & ({Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool}):
  ad.pick_bg(Ad.room(l, Ad.held(t)), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t), Ad.cnt(Ad.Holding{}, Ad.Ia{}, t), Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t), e)

def ad.bg_wb(-t: List<&2, Ad.Tk>, p: {Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t) == 0n : Nat} & ({Ad.cnt(Ad.Holding{}, Ad.Ia{}, t) == 0n : Nat} & {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool})) -> {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Bg{}, t)) == False{} : Bool}:
  (a, b, c) = p
  c

def aw.isz_bit(b: Bool, -n: Nat, e: {Ad.isz(n) == False{} : Bool}) -> {Ad.isz(Ad.bit(b, n)) == False{} : Bool}:
  match b:
    case False{}:
      e
    case True{}:
      {==}

def aw.wait0(h: Ad.Tk, -r: List<&2, Ad.Tk>, e: {Ad.waits.ia(Some{h}) == True{} : Bool}) -> {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, h <> r)) == False{} : Bool}:
  match h:
    case Ad.Tk{Ad.Ia{}, Ad.Queued{}}:
      {==}
    case Ad.Tk{Ad.Ia{}, Ad.Granted{}}:
      LALogic.ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Granted{}} <> r)) == False{} : Bool}, e)
    case Ad.Tk{Ad.Ia{}, Ad.Held{}}:
      LALogic.ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Held{}} <> r)) == False{} : Bool}, e)
    case Ad.Tk{Ad.Ia{}, Ad.Preempted{}}:
      LALogic.ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Preempted{}} <> r)) == False{} : Bool}, e)
    case Ad.Tk{Ad.Ia{}, Ad.Ended{}}:
      LALogic.ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Ia{}, Ad.Ended{}} <> r)) == False{} : Bool}, e)
    case Ad.Tk{Ad.Bg{}, s}:
      LALogic.ad.absurd({Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, Ad.Tk{Ad.Bg{}, s} <> r)) == False{} : Bool}, e)

# an interactive waiter is counted
def aw.wait_cnt(t: List<&2, Ad.Tk>, w: Nat, e: {Ad.waits.ia(Ad.get(t, w)) == True{} : Bool}) -> {Ad.isz(Ad.cnt(Ad.Waiting{}, Ad.Ia{}, t)) == False{} : Bool}:
  match t w:
    case Nil{} _:
      LALogic.ad.absurd({Ad.isz(0n) == False{} : Bool}, e)
    case +h <> +r 0n:
      aw.wait0(h, r, e)
    case +h <> +r 1n+p:
      aw.isz_bit(Ad.hit(Ad.Waiting{}, Ad.Ia{}, h), Ad.cnt(Ad.Waiting{}, Ad.Ia{}, r), aw.wait_cnt(r, p, e))
