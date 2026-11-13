# eukhe: the proof of LAW limits_set_wins
#
# PROOF: per dimension, a given limit picks the arm of set (lsw.v).

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB

# a given limit is taken, source set
def lsw.v(v: L.Val, -d: B.Dim, -t: L.Toggle, -ps: List<&2, L.Lims>, -own: L.Lims, -table: L.Lims, g: {S.given(v) == True{} : Bool}) -> {L.Pick{L.Pick.v(L.by_set(v, d, t, ps, own, table)), L.Pick.src(L.by_set(v, d, t, ps, own, table))} == L.Pick{v, L.Set{}} : L.Pick}:
  match v:
    case L.Unset{}:
      LB.lmb.absurd_ft({L.Pick{L.Pick.v(L.by_set(L.Unset{}, d, t, ps, own, table)), L.Pick.src(L.by_set(L.Unset{}, d, t, ps, own, table))} == L.Pick{L.Unset{}, L.Set{}} : L.Pick}, g)
    case L.At{x}:
      {==}
    case L.Unlimited{}:
      {==}

def Limits.limits_set_wins(t, k, a, set, ps, own, d, g):
  match set:
    case L.Lims{c, tk, m, n, r}:
      match d:
        case B.Cost{}:
          lsw.v(c, B.Cost{}, t, ps, own, L.profile(k, a), g)
        case B.Tok{}:
          lsw.v(tk, B.Tok{}, t, ps, own, L.profile(k, a), g)
        case B.Time{}:
          lsw.v(m, B.Time{}, t, ps, own, L.profile(k, a), g)
        case B.Calls{}:
          lsw.v(n, B.Calls{}, t, ps, own, L.profile(k, a), g)
        case B.Reqs{}:
          lsw.v(r, B.Reqs{}, t, ps, own, L.profile(k, a), g)
