# eukhe: the proof of LAW crown_help_spend_is_spec
#
# PROOF: induction on k with the help leaves (base/step.bend
# ac_step.spend_eq): at the head the code's checks are the spec's; past it
# both put the head back in front.

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/agent_crown.bend as A
import ../../spec/agents/agent_tree.bend as S
import ../../spec/agents/agent_crown.bend as CS
import ../../laws/agent_tree.bend as AgentTree
import ../../laws/agent_crown.bend as AgentCrown
import ./base/step.bend as St

def AgentCrown.crown_help_spend_is_spec(b, c, k, a):
  match c:
    case A.Crown{t, hs}:
      St.ac_step.spend_eq(k, hs, t, a)
