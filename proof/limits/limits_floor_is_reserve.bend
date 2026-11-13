# eukhe: the proof of LAW limits_floor_is_reserve
#
# PROOF: with every dimension a number, the floor and the reservation ask the same lack of the same need (lfr.m).

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB
import ../../spec/budget/ledger.bend as SL

# the reservation of the first request gives the floor's answer
def lfr.m(m: Maybe<&2, B.Dim>, x: B.Amt, +cm: Nat, -id: Nat, -base: B.Ask, -keep: B.Ask, -step: B.Ask, -free: B.Amt, -sp: B.Amt, -le: B.Amt, -ov: B.Amt, -hs: List<&2, B.Hold>, -until: Nat) -> {m == S.short(B.reserve.pick(B.pick.one(m, 0n, B.Ask{x, cm}), B.Work{}, B.Working{}, id, 0n, base, keep, step, free, sp, le, ov, hs, until)) : Maybe<&2, B.Dim>}:
  match m:
    case None{}:
      match x:
        case B.Amt{x1, x2, x3, x4}:
          {==}
    case Some{d}:
      {==}

def lfr.at(+c1: Nat, +c2: Nat, +c3: Nat, +c4: Nat, +cm: Nat, +k1: Nat, +k2: Nat, +k3: Nat, +k4: Nat, +km: Nat, v1: L.Val, v2: L.Val, v3: L.Val, v4: L.Val, v5: L.Val, +id: Nat, +step: B.Ask, h: {S.bounded(L.Lims{v1, v2, v3, v4, v5}) == True{} : Bool}) -> {L.floor(L.Lims{v1, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == S.short(B.reserve(B.Work{}, B.Working{}, id, 0n, SL.nothing(), B.Ask{B.Amt{k1, k2, k3, k4}, km}, step, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, Nil{}, S.fresh_acct(L.Lims{v1, v2, v3, v4, v5}))) : Maybe<&2, B.Dim>}:
  match v1:
    case L.Unset{}:
      LB.lmb.absurd_ft({L.floor(L.Lims{L.Unset{}, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == S.short(B.reserve(B.Work{}, B.Working{}, id, 0n, SL.nothing(), B.Ask{B.Amt{k1, k2, k3, k4}, km}, step, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, Nil{}, S.fresh_acct(L.Lims{L.Unset{}, v2, v3, v4, v5}))) : Maybe<&2, B.Dim>}, h)
    case L.At{a1}:
      match v2:
        case L.Unset{}:
          LB.lmb.absurd_ft({L.floor(L.Lims{L.At{a1}, L.Unset{}, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == S.short(B.reserve(B.Work{}, B.Working{}, id, 0n, SL.nothing(), B.Ask{B.Amt{k1, k2, k3, k4}, km}, step, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, Nil{}, S.fresh_acct(L.Lims{L.At{a1}, L.Unset{}, v3, v4, v5}))) : Maybe<&2, B.Dim>}, h)
        case L.At{a2}:
          match v3:
            case L.Unset{}:
              LB.lmb.absurd_ft({L.floor(L.Lims{L.At{a1}, L.At{a2}, L.Unset{}, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == S.short(B.reserve(B.Work{}, B.Working{}, id, 0n, SL.nothing(), B.Ask{B.Amt{k1, k2, k3, k4}, km}, step, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, Nil{}, S.fresh_acct(L.Lims{L.At{a1}, L.At{a2}, L.Unset{}, v4, v5}))) : Maybe<&2, B.Dim>}, h)
            case L.At{a3}:
              match v4:
                case L.Unset{}:
                  LB.lmb.absurd_ft({L.floor(L.Lims{L.At{a1}, L.At{a2}, L.At{a3}, L.Unset{}, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == S.short(B.reserve(B.Work{}, B.Working{}, id, 0n, SL.nothing(), B.Ask{B.Amt{k1, k2, k3, k4}, km}, step, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, Nil{}, S.fresh_acct(L.Lims{L.At{a1}, L.At{a2}, L.At{a3}, L.Unset{}, v5}))) : Maybe<&2, B.Dim>}, h)
                case L.At{a4}:
                  match v5:
                    case L.Unset{}:
                      LB.lmb.absurd_ft({L.floor(L.Lims{L.At{a1}, L.At{a2}, L.At{a3}, L.At{a4}, L.Unset{}}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == S.short(B.reserve(B.Work{}, B.Working{}, id, 0n, SL.nothing(), B.Ask{B.Amt{k1, k2, k3, k4}, km}, step, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, Nil{}, S.fresh_acct(L.Lims{L.At{a1}, L.At{a2}, L.At{a3}, L.At{a4}, L.Unset{}}))) : Maybe<&2, B.Dim>}, h)
                    case L.At{a5}:
                      lfr.m(B.lack(B.need(B.Work{}, SL.nothing(), B.Ask{B.Amt{k1, k2, k3, k4}, km}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}), B.Amt{a1, a2, a4, a5}, 0n, a3), B.Amt{c1, c2, c3, c4}, cm, id, SL.nothing(), B.Ask{B.Amt{k1, k2, k3, k4}, km}, step, B.Amt{a1, a2, a4, a5}, B.zero(), B.zero(), B.zero(), Nil{}, a3)
                    case L.Unlimited{}:
                      LB.lmb.absurd_ft({L.floor(L.Lims{L.At{a1}, L.At{a2}, L.At{a3}, L.At{a4}, L.Unlimited{}}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == S.short(B.reserve(B.Work{}, B.Working{}, id, 0n, SL.nothing(), B.Ask{B.Amt{k1, k2, k3, k4}, km}, step, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, Nil{}, S.fresh_acct(L.Lims{L.At{a1}, L.At{a2}, L.At{a3}, L.At{a4}, L.Unlimited{}}))) : Maybe<&2, B.Dim>}, h)
                case L.Unlimited{}:
                  LB.lmb.absurd_ft({L.floor(L.Lims{L.At{a1}, L.At{a2}, L.At{a3}, L.Unlimited{}, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == S.short(B.reserve(B.Work{}, B.Working{}, id, 0n, SL.nothing(), B.Ask{B.Amt{k1, k2, k3, k4}, km}, step, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, Nil{}, S.fresh_acct(L.Lims{L.At{a1}, L.At{a2}, L.At{a3}, L.Unlimited{}, v5}))) : Maybe<&2, B.Dim>}, h)
            case L.Unlimited{}:
              LB.lmb.absurd_ft({L.floor(L.Lims{L.At{a1}, L.At{a2}, L.Unlimited{}, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == S.short(B.reserve(B.Work{}, B.Working{}, id, 0n, SL.nothing(), B.Ask{B.Amt{k1, k2, k3, k4}, km}, step, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, Nil{}, S.fresh_acct(L.Lims{L.At{a1}, L.At{a2}, L.Unlimited{}, v4, v5}))) : Maybe<&2, B.Dim>}, h)
        case L.Unlimited{}:
          LB.lmb.absurd_ft({L.floor(L.Lims{L.At{a1}, L.Unlimited{}, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == S.short(B.reserve(B.Work{}, B.Working{}, id, 0n, SL.nothing(), B.Ask{B.Amt{k1, k2, k3, k4}, km}, step, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, Nil{}, S.fresh_acct(L.Lims{L.At{a1}, L.Unlimited{}, v3, v4, v5}))) : Maybe<&2, B.Dim>}, h)
    case L.Unlimited{}:
      LB.lmb.absurd_ft({L.floor(L.Lims{L.Unlimited{}, v2, v3, v4, v5}, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, B.Ask{B.Amt{k1, k2, k3, k4}, km}) == S.short(B.reserve(B.Work{}, B.Working{}, id, 0n, SL.nothing(), B.Ask{B.Amt{k1, k2, k3, k4}, km}, step, B.Ask{B.Amt{c1, c2, c3, c4}, cm}, Nil{}, S.fresh_acct(L.Lims{L.Unlimited{}, v2, v3, v4, v5}))) : Maybe<&2, B.Dim>}, h)

def Limits.limits_floor_is_reserve(l, c, keep, id, step, h):
  match l c keep:
    case L.Lims{v1, v2, v3, v4, v5} B.Ask{B.Amt{c1, c2, c3, c4}, cm} B.Ask{B.Amt{k1, k2, k3, k4}, km}:
      lfr.at(c1, c2, c3, c4, cm, k1, k2, k3, k4, km, v1, v2, v3, v4, v5, id, step, h)
