# eukhe: the proof of LAW crown_help_is_spec
#
# PROOF: the code's view and node lookup are the spec's; by the node's
# presence, then the checks in order, the code's decision is the spec's
# with T.free for S.room, T.size for S.nodes and hcount for count
# (base/step.bend ac_step.help_eq).

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/agent_crown.bend as A
import ../../spec/agents/agent_tree.bend as S
import ../../spec/agents/agent_crown.bend as CS
import ../../laws/agent_tree.bend as AgentTree
import ../../laws/agent_crown.bend as AgentCrown
import ./base/step.bend as St

def AgentCrown.crown_help_is_spec(b, c, p, a):
  match c:
    case A.Crown{t, hs}:
      St.ac_step.help_eq(b, t, hs, p, a)
