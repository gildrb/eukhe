# eukhe: the proof of LAW agent_tree_run_last
#
# PROOF: induction on evs, the tree generalized: with no event before e,
# run takes one step (after and landed agree on every step); with h first,
# both sides start from the tree h left.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree

def at_run.after_landed(s: T.Step, -t: T.Node) -> {T.after(s, t) == AgentTree.landed(s, t) : T.Node}:
  match s:
    case T.Took{n}:
      {==}
    case T.Refused{why}:
      {==}

def AgentTree.agent_tree_run_last(evs, e, b, t):
  match evs:
    case Nil{}:
      at_run.after_landed(T.step(b, t, e), t)
    case Con{h, hs}:
      AgentTree.agent_tree_run_last(hs, e, b, T.after(T.step(b, t, h), t))
