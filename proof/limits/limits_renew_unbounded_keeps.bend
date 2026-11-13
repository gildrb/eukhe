# eukhe: the proof of LAW limits_renew_unbounded_keeps
#
# PROOF: a spent dimension renews by its limit (lmb.free); without a number it keeps what is free (luk.v); time holds no amount.

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB
import ../../spec/budget/ledger.bend as SL

def luk.v(v: L.Val, -f: Nat, -x: Nat, h: {S.is_at(v) == False{} : Bool}) -> {L.renew.dim(v, f, x) == f : Nat}:
  match v:
    case L.Unset{}:
      {==}
    case L.At{n}:
      LB.lmb.absurd_tf({L.renew.dim(L.At{n}, f, x) == f : Nat}, h)
    case L.Unlimited{}:
      {==}

def luk.d(+d: B.Dim, +l: L.Lims, +f: B.Amt, +u: B.Amt, sd: {S.spent_dim(d) == True{} : Bool}, h: {S.is_at(S.dim(d, l)) == False{} : Bool}) -> {SL.at(d, L.renew.free(l, f, u)) == SL.at(d, f) : Nat}:
  Equal.trans(Nat, SL.at(d, L.renew.free(l, f, u)), L.renew.dim(S.dim(d, l), SL.at(d, f), SL.at(d, u)), SL.at(d, f), LB.lmb.free(d, l, f, u, sd), luk.v(S.dim(d, l), SL.at(d, f), SL.at(d, u), h))

def Limits.limits_renew_unbounded_keeps(l, mark, now, a, d, h):
  match a:
    case B.Acct{f, sp, le, o, hs, u}:
      match d:
            case B.Time{}:
              {==}
            case B.Cost{}:
              luk.d(B.Cost{}, l, f, B.add4(B.sub4(sp, mark), B.add4(L.holding(hs), le)), {==}, h)
            case B.Tok{}:
              luk.d(B.Tok{}, l, f, B.add4(B.sub4(sp, mark), B.add4(L.holding(hs), le)), {==}, h)
            case B.Calls{}:
              luk.d(B.Calls{}, l, f, B.add4(B.sub4(sp, mark), B.add4(L.holding(hs), le)), {==}, h)
            case B.Reqs{}:
              luk.d(B.Reqs{}, l, f, B.add4(B.sub4(sp, mark), B.add4(L.holding(hs), le)), {==}, h)
