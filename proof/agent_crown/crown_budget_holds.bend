# eukhe: the proof of LAW crown_budget_holds
#
# PROOF: the invariant (base/budget.bend ac_bud.CB): the view is Good (the
# tree's own invariant, agent_tree's base/reach.bend) with the root's scope
# and Value limit, every load's path names a node of the tree, and every
# running help leaf has a Value limit its spend fits. A tree event is the
# tree's step on the view (Good kept by at_reach.inv_step); the step only
# grows the tree (base/grow.bend), so taking the charges off and putting
# them back gives the step's tree, and the sweep only lowers charges,
# which keeps Good (ac_bud.good_lle). A help is a spend of its amount at
# its node on the view (under a Value root every running node's free is a
# Value, so the help leaf's limit and charge are the amount). A help
# leaf's spend keeps its charge; its end lowers it. Finally the view's
# spend is the tree's spend plus every charge, at least the help leaves'
# spend, and Good bounds it by the root's limit.

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/agent_crown.bend as A
import ../../spec/agents/agent_tree.bend as S
import ../../spec/agents/agent_crown.bend as CS
import ../../laws/agent_tree.bend as AgentTree
import ../../laws/agent_crown.bend as AgentCrown
import ./base/budget.bend as B

def AgentCrown.crown_budget_holds(evs, b, s, m, dl):
  B.ac_bud.budget(evs, b, s, m, dl)
