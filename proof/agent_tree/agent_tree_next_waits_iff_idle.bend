# eukhe: the proof of LAW agent_tree_next_waits_iff_idle
#
# PROOF: case analysis on the view's message, arrived count and own work; each case computes.

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/patch.bend as LP

def AgentTree.agent_tree_next_waits_iff_idle(v):
  match v:
    case T.View{m, n, w}:
      match m:
        case True{}:
          {==}
        case False{}:
          match n:
            case 0n:
              match w:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case 1n+p:
              {==}
