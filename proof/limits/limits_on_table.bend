# eukhe: the proof of LAW limits_on_table
#
# PROOF: a dimension neither set nor given by a preset goes by the toggle (lmb.by_set, lmb.none_case); on, with no profile value, the limits profile's (lot.v).

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB

# with no profile value, the limits profile's
def lot.v(v: L.Val, tb: L.Val, h: {S.given(v) == False{} : Bool}) -> {L.Pick{L.Pick.v(L.on.profile(v, tb)), L.Pick.src(L.on.profile(v, tb))} == S.table(tb) : L.Pick}:
  match v:
    case L.Unset{}:
      match tb:
        case L.Unset{}:
          {==}
        case L.At{x}:
          {==}
        case L.Unlimited{}:
          {==}
    case L.At{x}:
      LB.lmb.absurd_tf({L.Pick{L.Pick.v(L.on.profile(L.At{x}, tb)), L.Pick.src(L.on.profile(L.At{x}, tb))} == S.table(tb) : L.Pick}, h)
    case L.Unlimited{}:
      LB.lmb.absurd_tf({L.Pick{L.Pick.v(L.on.profile(L.Unlimited{}, tb)), L.Pick.src(L.on.profile(L.Unlimited{}, tb))} == S.table(tb) : L.Pick}, h)

def Limits.limits_on_table(k, a, set, ps, own, d, g, e, h):
  match set:
    case L.Lims{c, tk, m, n, r}:
      match d:
        case B.Cost{}:
          LB.lmb.by_set(c, B.Cost{}, L.On{}, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Cost{}, L.profile(k, a))) : L.Pick}, g, LB.lmb.none_case(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Cost{}, L.profile(k, a))) : L.Pick}, B.Cost{}, ps, L.On{}, L.get(B.Cost{}, own), L.get(B.Cost{}, L.profile(k, a)), e, LB.lmb.unset_get(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Cost{}, L.profile(k, a))) : L.Pick}, B.Cost{}, L.On{}, own, L.profile(k, a), lot.v(S.dim(B.Cost{}, own), S.dim(B.Cost{}, L.profile(k, a)), h))))
        case B.Tok{}:
          LB.lmb.by_set(tk, B.Tok{}, L.On{}, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Tok{}, L.profile(k, a))) : L.Pick}, g, LB.lmb.none_case(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Tok{}, L.profile(k, a))) : L.Pick}, B.Tok{}, ps, L.On{}, L.get(B.Tok{}, own), L.get(B.Tok{}, L.profile(k, a)), e, LB.lmb.unset_get(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Tok{}, L.profile(k, a))) : L.Pick}, B.Tok{}, L.On{}, own, L.profile(k, a), lot.v(S.dim(B.Tok{}, own), S.dim(B.Tok{}, L.profile(k, a)), h))))
        case B.Time{}:
          LB.lmb.by_set(m, B.Time{}, L.On{}, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Time{}, L.profile(k, a))) : L.Pick}, g, LB.lmb.none_case(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Time{}, L.profile(k, a))) : L.Pick}, B.Time{}, ps, L.On{}, L.get(B.Time{}, own), L.get(B.Time{}, L.profile(k, a)), e, LB.lmb.unset_get(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Time{}, L.profile(k, a))) : L.Pick}, B.Time{}, L.On{}, own, L.profile(k, a), lot.v(S.dim(B.Time{}, own), S.dim(B.Time{}, L.profile(k, a)), h))))
        case B.Calls{}:
          LB.lmb.by_set(n, B.Calls{}, L.On{}, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Calls{}, L.profile(k, a))) : L.Pick}, g, LB.lmb.none_case(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Calls{}, L.profile(k, a))) : L.Pick}, B.Calls{}, ps, L.On{}, L.get(B.Calls{}, own), L.get(B.Calls{}, L.profile(k, a)), e, LB.lmb.unset_get(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Calls{}, L.profile(k, a))) : L.Pick}, B.Calls{}, L.On{}, own, L.profile(k, a), lot.v(S.dim(B.Calls{}, own), S.dim(B.Calls{}, L.profile(k, a)), h))))
        case B.Reqs{}:
          LB.lmb.by_set(r, B.Reqs{}, L.On{}, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Reqs{}, L.profile(k, a))) : L.Pick}, g, LB.lmb.none_case(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Reqs{}, L.profile(k, a))) : L.Pick}, B.Reqs{}, ps, L.On{}, L.get(B.Reqs{}, own), L.get(B.Reqs{}, L.profile(k, a)), e, LB.lmb.unset_get(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == S.table(S.dim(B.Reqs{}, L.profile(k, a))) : L.Pick}, B.Reqs{}, L.On{}, own, L.profile(k, a), lot.v(S.dim(B.Reqs{}, own), S.dim(B.Reqs{}, L.profile(k, a)), h))))
