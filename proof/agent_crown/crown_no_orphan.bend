# eukhe: the proof of LAW crown_no_orphan
#
# PROOF: the root crown has no help leaf. Every event keeps every running
# help leaf at a running node (base/reach.bend ac_reach.step_placed): a
# tree event's sweep cancels every running help leaf whose node does not
# run in the new tree; a help is admitted only at a node that runs on the
# view, so in the tree (the view keeps every node's status); a help leaf's
# spend keeps its status and path; its end settles it.

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/agent_crown.bend as A
import ../../spec/agents/agent_tree.bend as S
import ../../spec/agents/agent_crown.bend as CS
import ../../laws/agent_tree.bend as AgentTree
import ../../laws/agent_crown.bend as AgentCrown
import ./base/reach.bend as R

def AgentCrown.crown_no_orphan(evs, b, s, lim, dl):
  R.ac_reach.run_placed_all(evs, b, A.cinit(s, lim, dl), {==})
