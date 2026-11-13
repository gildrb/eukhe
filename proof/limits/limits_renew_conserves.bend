# eukhe: the proof of LAW limits_renew_conserves
#
# PROOF: a spent dimension renews by its limit (lmb.free); what the code counts used is the spec's use (lmb.used); (n - x) + x is the larger of n and x (lmb.sub_add_max).

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB
import ../../spec/budget/ledger.bend as SL

def lrc.v(v: L.Val, -f: Nat, +x: Nat, h: {S.is_at(v) == True{} : Bool}) -> {Nat.add(L.renew.dim(v, f, x), x) == Nat.max(S.num(v), x) : Nat}:
  match v:
    case L.Unset{}:
      LB.lmb.absurd_ft({Nat.add(L.renew.dim(L.Unset{}, f, x), x) == Nat.max(S.num(L.Unset{}), x) : Nat}, h)
    case L.At{n}:
      LB.lmb.sub_add_max(n, x)
    case L.Unlimited{}:
      LB.lmb.absurd_ft({Nat.add(L.renew.dim(L.Unlimited{}, f, x), x) == Nat.max(S.num(L.Unlimited{}), x) : Nat}, h)

def lrc.d(+d: B.Dim, +l: L.Lims, +f: B.Amt, +sp: B.Amt, +mark: B.Amt, +hs: List<&2, B.Hold>, +le: B.Amt, sd: {S.spent_dim(d) == True{} : Bool}, h: {S.is_at(S.dim(d, l)) == True{} : Bool}) -> {Nat.add(SL.at(d, L.renew.free(l, f, B.add4(B.sub4(sp, mark), B.add4(L.holding(hs), le)))), Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), Nat.add(SL.held(d, hs), SL.at(d, le)))) == Nat.max(S.num(S.dim(d, l)), Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), Nat.add(SL.held(d, hs), SL.at(d, le)))) : Nat}:
  %Equal.sym(Nat, SL.at(d, L.renew.free(l, f, B.add4(B.sub4(sp, mark), B.add4(L.holding(hs), le)))), L.renew.dim(S.dim(d, l), SL.at(d, f), SL.at(d, B.add4(B.sub4(sp, mark), B.add4(L.holding(hs), le)))), LB.lmb.free(d, l, f, B.add4(B.sub4(sp, mark), B.add4(L.holding(hs), le)), sd)) : {Nat.add(_, Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), Nat.add(SL.held(d, hs), SL.at(d, le)))) == Nat.max(S.num(S.dim(d, l)), Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), Nat.add(SL.held(d, hs), SL.at(d, le)))) : Nat}
  %Equal.sym(Nat, SL.at(d, B.add4(B.sub4(sp, mark), B.add4(L.holding(hs), le))), Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), Nat.add(SL.held(d, hs), SL.at(d, le))), LB.lmb.used(d, sp, mark, hs, le)) : {Nat.add(L.renew.dim(S.dim(d, l), SL.at(d, f), _), Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), Nat.add(SL.held(d, hs), SL.at(d, le)))) == Nat.max(S.num(S.dim(d, l)), Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), Nat.add(SL.held(d, hs), SL.at(d, le)))) : Nat}
  lrc.v(S.dim(d, l), SL.at(d, f), Nat.add(Nat.sub(SL.at(d, sp), SL.at(d, mark)), Nat.add(SL.held(d, hs), SL.at(d, le))), h)

def Limits.limits_renew_conserves(l, mark, now, a, d, sd, h):
  match a:
    case B.Acct{f, sp, le, o, hs, u}:
      match d:
            case B.Time{}:
              LB.lmb.absurd_ft({Nat.add(SL.at(B.Time{}, SL.free(L.renew(l, mark, now, B.Acct{f, sp, le, o, hs, u}))), S.use(B.Time{}, mark, B.Acct{f, sp, le, o, hs, u})) == Nat.max(S.num(S.dim(B.Time{}, l)), S.use(B.Time{}, mark, B.Acct{f, sp, le, o, hs, u})) : Nat}, sd)
            case B.Cost{}:
              lrc.d(B.Cost{}, l, f, sp, mark, hs, le, sd, h)
            case B.Tok{}:
              lrc.d(B.Tok{}, l, f, sp, mark, hs, le, sd, h)
            case B.Calls{}:
              lrc.d(B.Calls{}, l, f, sp, mark, hs, le, sd, h)
            case B.Reqs{}:
              lrc.d(B.Reqs{}, l, f, sp, mark, hs, le, sd, h)
