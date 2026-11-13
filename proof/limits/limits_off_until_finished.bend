# eukhe: the proof of LAW limits_off_until_finished
#
# PROOF: a dimension neither set nor given by a preset goes by the toggle (lmb.by_set, lmb.none_case); off is until finished.

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB

def Limits.limits_off_until_finished(k, a, set, ps, own, d, g, e):
  match set:
    case L.Lims{c, tk, m, n, r}:
      match d:
        case B.Cost{}:
          LB.lmb.by_set(c, B.Cost{}, L.Off{}, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == L.Pick{L.Unlimited{}, L.UntilFinished{}} : L.Pick}, g, LB.lmb.none_case(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == L.Pick{L.Unlimited{}, L.UntilFinished{}} : L.Pick}, B.Cost{}, ps, L.Off{}, L.get(B.Cost{}, own), L.get(B.Cost{}, L.profile(k, a)), e, {==}))
        case B.Tok{}:
          LB.lmb.by_set(tk, B.Tok{}, L.Off{}, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == L.Pick{L.Unlimited{}, L.UntilFinished{}} : L.Pick}, g, LB.lmb.none_case(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == L.Pick{L.Unlimited{}, L.UntilFinished{}} : L.Pick}, B.Tok{}, ps, L.Off{}, L.get(B.Tok{}, own), L.get(B.Tok{}, L.profile(k, a)), e, {==}))
        case B.Time{}:
          LB.lmb.by_set(m, B.Time{}, L.Off{}, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == L.Pick{L.Unlimited{}, L.UntilFinished{}} : L.Pick}, g, LB.lmb.none_case(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == L.Pick{L.Unlimited{}, L.UntilFinished{}} : L.Pick}, B.Time{}, ps, L.Off{}, L.get(B.Time{}, own), L.get(B.Time{}, L.profile(k, a)), e, {==}))
        case B.Calls{}:
          LB.lmb.by_set(n, B.Calls{}, L.Off{}, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == L.Pick{L.Unlimited{}, L.UntilFinished{}} : L.Pick}, g, LB.lmb.none_case(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == L.Pick{L.Unlimited{}, L.UntilFinished{}} : L.Pick}, B.Calls{}, ps, L.Off{}, L.get(B.Calls{}, own), L.get(B.Calls{}, L.profile(k, a)), e, {==}))
        case B.Reqs{}:
          LB.lmb.by_set(r, B.Reqs{}, L.Off{}, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == L.Pick{L.Unlimited{}, L.UntilFinished{}} : L.Pick}, g, LB.lmb.none_case(x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == L.Pick{L.Unlimited{}, L.UntilFinished{}} : L.Pick}, B.Reqs{}, ps, L.Off{}, L.get(B.Reqs{}, own), L.get(B.Reqs{}, L.profile(k, a)), e, {==}))
