# eukhe: the proof of LAW agent_tree_init_admits
#
# PROOF: the root is a running leaf with nothing spent, so the spend is
# decided on lim_fits(a, lim less 0) (at_init.fits_spend); case on lim:
# Unlimited fits everything, a Value m less 0 is m

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree

# a spend decision is admitted exactly when its fit is true
def at_init.fits_spend(x: Bool, t: T.Node, a: Nat) -> {AgentTree.admitted(T.spend_fits(x, t, a)) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def AgentTree.agent_tree_init_admits(b, s, lim, dl, a):
  match lim:
    case T.Unlimited{}:
      at_init.fits_spend(True{}, T.init(s, T.Unlimited{}, dl), a)
    case T.Value{m}:
      match m:
        case 0n:
          at_init.fits_spend(Nat.is_le(a, 0n), T.init(s, T.Value{0n}, dl), a)
        case 1n+p:
          at_init.fits_spend(Nat.is_le(a, 1n+p), T.init(s, T.Value{1n+p}, dl), a)
