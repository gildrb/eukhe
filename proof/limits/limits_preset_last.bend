# eukhe: the proof of LAW limits_preset_last
#
# PROOF: a dimension left unset goes by the presets (lmb.by_set); the code's last preset is the spec's (lmb.last0); the pick read back is the pick.

import Base
import ../../bend/budget.bend as B
import ../../bend/limits.bend as L
import ../../laws/limits.bend as Limits
import ../../spec/budget/limits.bend as S
import ./base.bend as LB

# the last preset's pick, read back
def lpl.k(+d: B.Dim, +ps: List<&2, L.Lims>, -t: L.Toggle, -o: L.Val, -tb: L.Val, +p: L.Pick, e: {S.last(d, ps) == Some{p} : Maybe<&2, L.Pick>}) -> {L.Pick{L.Pick.v(L.by_preset(L.last(d, ps, 0n, None{}), t, o, tb)), L.Pick.src(L.by_preset(L.last(d, ps, 0n, None{}), t, o, tb))} == p : L.Pick}:
  %Equal.sym(Maybe<&2, L.Pick>, L.last(d, ps, 0n, None{}), S.last(d, ps), LB.lmb.last0(d, ps)) : {L.Pick{L.Pick.v(L.by_preset(_, t, o, tb)), L.Pick.src(L.by_preset(_, t, o, tb))} == p : L.Pick}
  %Equal.sym(Maybe<&2, L.Pick>, S.last(d, ps), Some{p}, e) : {L.Pick{L.Pick.v(L.by_preset(_, t, o, tb)), L.Pick.src(L.by_preset(_, t, o, tb))} == p : L.Pick}
  LB.lmb.eta(p)

def Limits.limits_preset_last(t, k, a, set, ps, own, d, p, g, e):
  match set:
    case L.Lims{c, tk, m, n, r}:
      match d:
        case B.Cost{}:
          LB.lmb.by_set(c, B.Cost{}, t, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == p : L.Pick}, g, lpl.k(B.Cost{}, ps, t, L.get(B.Cost{}, own), L.get(B.Cost{}, L.profile(k, a)), p, e))
        case B.Tok{}:
          LB.lmb.by_set(tk, B.Tok{}, t, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == p : L.Pick}, g, lpl.k(B.Tok{}, ps, t, L.get(B.Tok{}, own), L.get(B.Tok{}, L.profile(k, a)), p, e))
        case B.Time{}:
          LB.lmb.by_set(m, B.Time{}, t, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == p : L.Pick}, g, lpl.k(B.Time{}, ps, t, L.get(B.Time{}, own), L.get(B.Time{}, L.profile(k, a)), p, e))
        case B.Calls{}:
          LB.lmb.by_set(n, B.Calls{}, t, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == p : L.Pick}, g, lpl.k(B.Calls{}, ps, t, L.get(B.Calls{}, own), L.get(B.Calls{}, L.profile(k, a)), p, e))
        case B.Reqs{}:
          LB.lmb.by_set(r, B.Reqs{}, t, ps, own, L.profile(k, a), x => {L.Pick{L.Pick.v(x), L.Pick.src(x)} == p : L.Pick}, g, lpl.k(B.Reqs{}, ps, t, L.get(B.Reqs{}, own), L.get(B.Reqs{}, L.profile(k, a)), p, e))
