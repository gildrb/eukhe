# eukhe: the proof of LAW crown_tree_is_spec
#
# PROOF: the code's bounds and view are the spec's (base/step.bend
# ac_step.bounds_eq, base/view.bend ac_view.view_eq); taken, the code's
# shift down is the spec's unview (ac_view.unview_eq) and its sweep the
# spec's (ac_step.sweep_eq).

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/agent_crown.bend as A
import ../../spec/agents/agent_tree.bend as S
import ../../spec/agents/agent_crown.bend as CS
import ../../laws/agent_tree.bend as AgentTree
import ../../laws/agent_crown.bend as AgentCrown
import ./base/step.bend as St

def AgentCrown.crown_tree_is_spec(b, c, e):
  match c:
    case A.Crown{t, hs}:
      St.ac_step.tree_eq(b, t, hs, e)
