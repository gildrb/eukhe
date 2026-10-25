# eukhe: the proof of LAW tree_commit_parent_first

import Base
import ../../bend/tree_commit.bend as Tc
import ../../bend/ffi_tree_commit.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/tree_commit.bend as TreeCommit
import ./base.bend as LATreeCommit
import ./tree_commit_order_exact.bend as PTreeCommitOrderExact

# PROOF of LAW tree_commit_parent_first: the order is the spec's (tree_commit_order_exact); a pass applies a Put only when its parent is present and makes its key present, as the walk checks (tcp.pass); unknown parents and Dels pass the walk (tcp.unknowns, tcp.dels); the rounds follow (tcp.rounds).

# the Dels pass the walk
def tcp.dels(cs0: List<&2, Tc.Ch>, +k: Nat, -cs: List<&2, Tc.Ch>, -rd: List<&2, Nat>) -> {TreeCommit.justified(TreeCommit.dels_spec(cs0, k), cs, rd) == True{} : Bool}:
  match cs0:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case Tc.Here{x}:
          tcp.dels(t, 1n+k, cs, rd)
        case Tc.Under{x, y}:
          tcp.dels(t, 1n+k, cs, rd)
        case Tc.Gone{}:
          tcp.dels(t, 1n+k, cs, rd)

# unknown parents pass the walk
def tcp.unknowns(ps: List<&2, Nat>, -ys: List<&2, Tc.Res>, -cs: List<&2, Tc.Ch>, -rd: List<&2, Nat>) -> {TreeCommit.justified(List.append(&2, Tc.Res, TreeCommit.unknowns(ps), ys), cs, rd) == TreeCommit.justified(ys, cs, rd) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> t:
      tcp.unknowns(t, ys, cs, rd)

# a Put applied when its parent is present (b, eb) or still waiting
def tcp.cons(b: Bool, +j: Nat, p: TreeCommit.Pass, -ys: List<&2, Tc.Res>, +cs: List<&2, Tc.Ch>, +ready: List<&2, Nat>, eb: {TreeCommit.parent_in(ready, TreeCommit.at(cs, j)) == b : Bool}, ih: {TreeCommit.justified(List.append(&2, Tc.Res, TreeCommit.applies(TreeCommit.Pass.applied(p)), ys), cs, TreeCommit.add_if(b, TreeCommit.key_of(TreeCommit.at(cs, j)), ready)) == TreeCommit.justified(ys, cs, TreeCommit.Pass.ready(p)) : Bool}) -> {TreeCommit.justified(List.append(&2, Tc.Res, TreeCommit.applies(TreeCommit.Pass.applied(TreeCommit.pass.cons(b, j, p))), ys), cs, ready) == TreeCommit.justified(ys, cs, TreeCommit.Pass.ready(TreeCommit.pass.cons(b, j, p))) : Bool}:
  match b:
    case True{}:
      match p:
        case TreeCommit.Pass{a, w, rd}:
          %Equal.sym(Bool, TreeCommit.parent_in(ready, TreeCommit.at(cs, j)), True{}, eb) : {TreeCommit.justified.go(_, TreeCommit.justified(List.append(&2, Tc.Res, TreeCommit.applies(a), ys), cs, TreeCommit.key_of(TreeCommit.at(cs, j)) <> ready)) == TreeCommit.justified(ys, cs, rd) : Bool}
          ih
    case False{}:
      match p:
        case TreeCommit.Pass{a, w, rd}:
          ih

# a pass's applied Puts pass the walk, and leave the keys of the pass
def tcp.pass(ps: List<&2, Nat>, -ys: List<&2, Tc.Res>, +cs: List<&2, Tc.Ch>, +ready: List<&2, Nat>) -> {TreeCommit.justified(List.append(&2, Tc.Res, TreeCommit.applies(TreeCommit.Pass.applied(TreeCommit.pass(ps, cs, ready))), ys), cs, ready) == TreeCommit.justified(ys, cs, TreeCommit.Pass.ready(TreeCommit.pass(ps, cs, ready))) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +j <> +t:
      +c = TreeCommit.at(cs, j)
      +b = TreeCommit.parent_in(ready, c)
      +r = TreeCommit.add_if(b, TreeCommit.key_of(c), ready)
      tcp.cons(b, j, TreeCommit.pass(t, cs, r), ys, cs, ready, {==}, tcp.pass(t, ys, cs, r))

def tcp.pick(p: TreeCommit.Pass, +cs: List<&2, Tc.Ch>, +ready: List<&2, Nat>, +rs: List<&2, Tc.Res>, j2: {TreeCommit.justified(List.append(&2, Tc.Res, TreeCommit.applies(TreeCommit.Pass.applied(p)), List.append(&2, Tc.Res, rs, TreeCommit.dels_spec(cs, 0n))), cs, ready) == TreeCommit.justified(List.append(&2, Tc.Res, rs, TreeCommit.dels_spec(cs, 0n)), cs, TreeCommit.Pass.ready(p)) : Bool}, ih: {TreeCommit.justified(List.append(&2, Tc.Res, rs, TreeCommit.dels_spec(cs, 0n)), cs, TreeCommit.Pass.ready(p)) == True{} : Bool}) -> {TreeCommit.justified(List.append(&2, Tc.Res, TreeCommit.rounds.pick(TreeCommit.Pass.applied(p), TreeCommit.Pass.waiting(p), rs), TreeCommit.dels_spec(cs, 0n)), cs, ready) == True{} : Bool}:
  match p:
    case TreeCommit.Pass{a, w, rd}:
      match a:
        case Nil{}:
          Equal.trans(Bool, TreeCommit.justified(List.append(&2, Tc.Res, TreeCommit.unknowns(w), TreeCommit.dels_spec(cs, 0n)), cs, ready), TreeCommit.justified(TreeCommit.dels_spec(cs, 0n), cs, ready), True{}, tcp.unknowns(w, TreeCommit.dels_spec(cs, 0n), cs, ready), tcp.dels(cs, 0n, cs, ready))
        case +x <> +y:
          %Equal.sym(List<&2, Tc.Res>, List.append(&2, Tc.Res, List.append(&2, Tc.Res, TreeCommit.applies(x <> y), rs), TreeCommit.dels_spec(cs, 0n)), List.append(&2, Tc.Res, TreeCommit.applies(x <> y), List.append(&2, Tc.Res, rs, TreeCommit.dels_spec(cs, 0n))), LATreeCommit.tc.app_assoc(TreeCommit.applies(x <> y), rs, TreeCommit.dels_spec(cs, 0n))) : {TreeCommit.justified(_, cs, ready) == True{} : Bool}
          Equal.trans(Bool, TreeCommit.justified(List.append(&2, Tc.Res, TreeCommit.applies(x <> y), List.append(&2, Tc.Res, rs, TreeCommit.dels_spec(cs, 0n))), cs, ready), TreeCommit.justified(List.append(&2, Tc.Res, rs, TreeCommit.dels_spec(cs, 0n)), cs, rd), True{}, j2, ih)

# the rounds pass the walk, then the Dels
def tcp.rounds(f: Nat, +cs: List<&2, Tc.Ch>, +ready: List<&2, Nat>, +ps: List<&2, Nat>) -> {TreeCommit.justified(List.append(&2, Tc.Res, TreeCommit.rounds_spec(f, cs, ready, ps), TreeCommit.dels_spec(cs, 0n)), cs, ready) == True{} : Bool}:
  match f:
    case 0n:
      Equal.trans(Bool, TreeCommit.justified(List.append(&2, Tc.Res, TreeCommit.unknowns(ps), TreeCommit.dels_spec(cs, 0n)), cs, ready), TreeCommit.justified(TreeCommit.dels_spec(cs, 0n), cs, ready), True{}, tcp.unknowns(ps, TreeCommit.dels_spec(cs, 0n), cs, ready), tcp.dels(cs, 0n, cs, ready))
    case 1n++g:
      +p = TreeCommit.pass(ps, cs, ready)
      +rs = TreeCommit.rounds_spec(g, cs, TreeCommit.Pass.ready(p), TreeCommit.Pass.waiting(p))
      tcp.pick(p, cs, ready, rs, tcp.pass(ps, List.append(&2, Tc.Res, rs, TreeCommit.dels_spec(cs, 0n)), cs, ready), tcp.rounds(g, cs, TreeCommit.Pass.ready(p), TreeCommit.Pass.waiting(p)))

def TreeCommit.tree_commit_parent_first(cs):
  %Equal.sym(List<&2, Tc.Res>, Tc.order(cs), TreeCommit.order_spec(cs), TreeCommit.tree_commit_order_exact(cs)) : {TreeCommit.justified(_, cs, []) == True{} : Bool}
  tcp.rounds(List.length(&2, Tc.Ch, cs), cs, [], TreeCommit.put_indices(cs, 0n))
