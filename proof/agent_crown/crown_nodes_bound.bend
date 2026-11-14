# eukhe: the proof of LAW crown_nodes_bound
#
# PROOF: the root crown has one node and no help leaf. Every event keeps
# the nodes plus the help leaves within max_nodes (base/reach.bend
# ac_reach.step_nb): a tree event's step under max_nodes less the help
# leaves adds only the nodes its room allows (base/grow.bend
# ac_grow.size_step, no tree invariant needed), and the view and its
# undoing keep the tree's size; a help is admitted only with room for one
# more; a help leaf's spend or end keeps their count.

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/agent_crown.bend as A
import ../../spec/agents/agent_tree.bend as S
import ../../spec/agents/agent_crown.bend as CS
import ../../laws/agent_tree.bend as AgentTree
import ../../laws/agent_crown.bend as AgentCrown
import ./base/reach.bend as R

def ac_nb.bound(+evs: List<&2, A.CEv>, +b: T.Bounds, +s: List<&2, Bool>, +lim: T.Lim, +dl: T.Lim, e: {Nat.is_le(1n, T.bound_nodes(b)) == True{} : Bool}) -> {Nat.is_le(CS.crown_nodes(A.crun(evs, b, A.cinit(s, lim, dl))), T.bound_nodes(b)) == True{} : Bool}:
  %Equal.sym(Bool, Nat.is_le(CS.crown_nodes(A.crun(evs, b, A.cinit(s, lim, dl))), T.bound_nodes(b)), R.ac_reach.nb(A.crun(evs, b, A.cinit(s, lim, dl)), T.bound_nodes(b)), R.ac_reach.nodes_eq(A.crun(evs, b, A.cinit(s, lim, dl)), T.bound_nodes(b))) : {_ == True{} : Bool}
  R.ac_reach.run_nb_all(evs, b, A.cinit(s, lim, dl), e)

def AgentCrown.crown_nodes_bound(evs, b, s, lim, dl, e):
  ac_nb.bound(evs, b, s, lim, dl, e)
