# eukhe: the proof of LAW crown_help_overlay_nothing
#
# PROOF: a help leaf's scope is empty; overlay with the empty scope keeps
# cur by its cases, and conflicts with it is writes, by induction on a.

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/agent_crown.bend as A
import ../../spec/agents/agent_tree.bend as S
import ../../spec/agents/agent_crown.bend as CS
import ../../laws/agent_tree.bend as AgentTree
import ../../laws/agent_crown.bend as AgentCrown

def ac_ov.overlay_nil(cur: List<&2, Maybe<&2, Nat>>, a: List<&2, Maybe<&2, Nat>>) -> {T.overlay(cur, a, []) == cur : List<&2, Maybe<&2, Nat>>}:
  match cur:
    case Nil{}:
      match a:
        case Nil{}:
          {==}
        case Con{x, xt}:
          {==}
    case Con{c, ct}:
      match a:
        case Nil{}:
          {==}
        case Con{x, xt}:
          {==}

def ac_ov.conflicts_nil(a: List<&2, Maybe<&2, Nat>>) -> {T.conflicts(a, []) == S.writes(a) : List<&2, Bool>}:
  match a:
    case Nil{}:
      {==}
    case Con{x, xt}:
      match x:
        case None{}:
          Equal.cong(List<&2, Bool>, List<&2, Bool>, ys => False{} <> ys, T.conflicts(xt, []), S.writes(xt), ac_ov.conflicts_nil(xt))
        case Some{v}:
          Equal.cong(List<&2, Bool>, List<&2, Bool>, ys => True{} <> ys, T.conflicts(xt, []), S.writes(xt), ac_ov.conflicts_nil(xt))

def AgentCrown.crown_help_overlay_nothing(h, cur, a):
  match h:
    case A.Help{p, st, lim, sp, dl}:
      (ac_ov.overlay_nil(cur, a), ac_ov.conflicts_nil(a))
