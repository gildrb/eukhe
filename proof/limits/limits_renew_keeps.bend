# eukhe: the proof of LAW limits_renew_keeps
#
# PROOF: the renewal rebuilds the account with its spent, lent, overrun and holds; its deadline is the spec's per time limit (lrk.until).

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB
import ../../spec/budget/ledger.bend as SL

def lrk.until(m: L.Val, -now: Nat, -u: Nat) -> {L.renew.until(m, now, u) == S.deadline(m, now, u) : Nat}:
  match m:
    case L.Unset{}:
      {==}
    case L.At{x}:
      {==}
    case L.Unlimited{}:
      {==}

def Limits.limits_renew_keeps(l, mark, now, a):
  match l:
    case L.Lims{c, k, m, n, r}:
      match a:
        case B.Acct{f, sp, le, o, hs, u}:
          %Equal.sym(Nat, L.renew.until(m, now, u), S.deadline(m, now, u), lrk.until(m, now, u)) : {(sp, (le, (o, (hs, _)))) == (sp, (le, (o, (hs, S.deadline(m, now, u))))) : B.Amt & (B.Amt & (B.Amt & (List<&2, B.Hold> & Nat)))}
          {==}
