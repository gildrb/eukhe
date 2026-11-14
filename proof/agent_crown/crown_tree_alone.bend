# eukhe: the proof of LAW crown_tree_alone
#
# PROOF: with no help leaf the bounds keep max_nodes (n - 0 = n), the view
# is the tree and its undoing the new tree (base/view.bend
# ac_view.shift_nil), and the sweep of no help leaf is none.

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/agent_crown.bend as A
import ../../spec/agents/agent_tree.bend as S
import ../../spec/agents/agent_crown.bend as CS
import ../../laws/agent_tree.bend as AgentTree
import ../../laws/agent_crown.bend as AgentCrown
import ./base/view.bend as V

def ac_alone.bounds_nil(b: T.Bounds) -> {A.cbounds(b, []) == b : T.Bounds}:
  match b:
    case T.Bounds{d, n, m}:
      Equal.cong(Nat, T.Bounds, x => T.Bounds{d, x, m}, Nat.sub(n, 0n), n, V.ac_view.sub_zero(n))

def ac_alone.on_nil(+s: T.Step, -e: T.Ev) -> {A.on_tree(s, [], e) == AgentCrown.lifted(s) : A.CStep}:
  match s:
    case T.Took{x}:
      Equal.cong(T.Node, A.CStep, y => A.CTook{A.Crown{y, []}}, A.shift(x, [], False{}), x, V.ac_view.shift_nil(x, False{}))
    case T.Refused{why}:
      {==}

def AgentCrown.crown_tree_alone(b, t, e):
  %ac_alone.bounds_nil(b) : {A.on_tree(T.step(A.cbounds(b, []), A.shift(t, [], True{}), e), [], e) == AgentCrown.lifted(T.step(_, t, e)) : A.CStep}
  %V.ac_view.shift_nil(t, True{}) : {A.on_tree(T.step(A.cbounds(b, []), A.shift(t, [], True{}), e), [], e) == AgentCrown.lifted(T.step(A.cbounds(b, []), _, e)) : A.CStep}
  ac_alone.on_nil(T.step(A.cbounds(b, []), A.shift(t, [], True{}), e), e)
