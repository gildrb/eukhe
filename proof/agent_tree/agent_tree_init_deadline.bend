# eukhe: the proof of LAW agent_tree_init_deadline
#
# PROOF: the tick of a running leaf cancels it exactly when its deadline
# is up (at_init.tick_leaf); case on dl: Unlimited is never up, a Value d
# is up when d <= now

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree

# a running leaf after a tick with the flag u runs exactly when u is false
def at_init.tick_leaf(u: Bool, s: List<&2, Bool>, lim: T.Lim, dl: T.Lim) -> {S.is_running(T.Leaf{T.tick_info(u, T.Info{T.Running{}, s, lim, 0n, dl, []})}) == Bool.not(u) : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def AgentTree.agent_tree_init_deadline(b, s, lim, dl, now):
  match dl:
    case T.Unlimited{}:
      at_init.tick_leaf(False{}, s, lim, T.Unlimited{})
    case T.Value{d}:
      at_init.tick_leaf(Nat.is_le(d, now), s, lim, T.Value{d})
