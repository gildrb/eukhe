# eukhe: the proof of LAW crown_run_last
#
# PROOF: induction on evs, the crown generalized: with no event before e,
# crun takes one step (cafter and clanded agree on every step); with h
# first, both sides start from the crown h left.

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/agent_crown.bend as A
import ../../spec/agents/agent_tree.bend as S
import ../../spec/agents/agent_crown.bend as CS
import ../../laws/agent_tree.bend as AgentTree
import ../../laws/agent_crown.bend as AgentCrown

def ac_run.after_landed(s: A.CStep, -c: A.Crown) -> {A.cafter(s, c) == AgentCrown.clanded(s, c) : A.Crown}:
  match s:
    case A.CTook{n}:
      {==}
    case A.CRefused{why}:
      {==}

def AgentCrown.crown_run_last(evs, e, b, c):
  match evs:
    case Nil{}:
      ac_run.after_landed(A.hstep(b, c, e), c)
    case Con{h, hs}:
      AgentCrown.crown_run_last(hs, e, b, A.cafter(A.hstep(b, c, h), c))
