# eukhe: the proof of LAW agent_tree_result_integrates
#
# PROOF: the split's patch is its children's overlays, then its own patch
# (seq_apply_r); each overlay applies the child's writes inside its scope
# (overlay_applies_r); the empty base patch leaves the files
# (agent_tree_apply_ends)

import Base
import ../../bend/agent_tree.bend as T
import ../../spec/agents/agent_tree.bend as S
import ../../laws/agent_tree.bend as AgentTree
import ./base/patch.bend as LP
import ./agent_tree_apply_ends.bend as Ends

def AgentTree.agent_tree_result_integrates(i, own, l, r, f):
  %LP.at_patch.seq_apply_r(f, T.overlay(T.overlay([], T.result(l), T.scope_of(T.info(l))), T.result(r), T.scope_of(T.info(r))), T.patch_of(i)) : {_ == T.apply(T.apply(T.apply(f, S.restrict(T.result(l), T.scope_of(T.info(l)))), S.restrict(T.result(r), T.scope_of(T.info(r)))), T.patch_of(i)) : List<&2, Nat>}
  %LP.at_patch.overlay_applies_r(f, T.overlay([], T.result(l), T.scope_of(T.info(l))), T.result(r), T.scope_of(T.info(r))) : {T.apply(_, T.patch_of(i)) == T.apply(T.apply(T.apply(f, S.restrict(T.result(l), T.scope_of(T.info(l)))), S.restrict(T.result(r), T.scope_of(T.info(r)))), T.patch_of(i)) : List<&2, Nat>}
  %LP.at_patch.overlay_applies_r(f, [], T.result(l), T.scope_of(T.info(l))) : {T.apply(T.apply(_, S.restrict(T.result(r), T.scope_of(T.info(r)))), T.patch_of(i)) == T.apply(T.apply(T.apply(f, S.restrict(T.result(l), T.scope_of(T.info(l)))), S.restrict(T.result(r), T.scope_of(T.info(r)))), T.patch_of(i)) : List<&2, Nat>}
  %Equal.sym(List<&2, Nat>, T.apply(f, []), f, AgentTree.agent_tree_apply_ends(f)) : {T.apply(T.apply(T.apply(_, S.restrict(T.result(l), T.scope_of(T.info(l)))), S.restrict(T.result(r), T.scope_of(T.info(r)))), T.patch_of(i)) == T.apply(T.apply(T.apply(f, S.restrict(T.result(l), T.scope_of(T.info(l)))), S.restrict(T.result(r), T.scope_of(T.info(r)))), T.patch_of(i)) : List<&2, Nat>}
  {==}
