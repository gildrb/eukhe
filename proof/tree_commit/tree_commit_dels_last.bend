# eukhe: the proof of LAW tree_commit_dels_last

import Base
import ../../bend/tree_commit.bend as Tc
import ../../bend/ffi_tree_commit.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/tree_commit.bend as TreeCommit
import ./base.bend as LATreeCommit
import ./tree_commit_order_exact.bend as PTreeCommitOrderExact

# PROOF of LAW tree_commit_dels_last: the order is the spec's (tree_commit_order_exact): rounds whose results are all a Put's (tdl.rounds), then the Dels, which start with a Del or are empty (tdl.dels).

# the results are all a Put's (applied or unknown parent)
def tdl.allput(rs: List<&2, Tc.Res>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> t:
      match r:
        case Tc.Apply{i}:
          tdl.allput(t)
        case Tc.Orphan{i}:
          tdl.allput(t)
        case Tc.Retire{i}:
          False{}

def tdl.unknowns(ps: List<&2, Nat>) -> {tdl.allput(TreeCommit.unknowns(ps)) == True{} : Bool}:
  match ps:
    case Nil{}:
      {==}
    case p <> t:
      tdl.unknowns(t)

def tdl.applies(a: List<&2, Nat>, -rs: List<&2, Tc.Res>, h: {tdl.allput(rs) == True{} : Bool}) -> {tdl.allput(List.append(&2, Tc.Res, TreeCommit.applies(a), rs)) == True{} : Bool}:
  match a:
    case Nil{}:
      h
    case x <> t:
      tdl.applies(t, rs, h)

def tdl.pick(p: TreeCommit.Pass, -rs: List<&2, Tc.Res>, h: {tdl.allput(rs) == True{} : Bool}) -> {tdl.allput(TreeCommit.rounds.pick(TreeCommit.Pass.applied(p), TreeCommit.Pass.waiting(p), rs)) == True{} : Bool}:
  match p:
    case TreeCommit.Pass{a, w, rd}:
      match a:
        case Nil{}:
          tdl.unknowns(w)
        case x <> t:
          tdl.applies(x <> t, rs, h)

# the rounds answer only Puts
def tdl.rounds(f: Nat, +cs: List<&2, Tc.Ch>, +ready: List<&2, Nat>, +ps: List<&2, Nat>) -> {tdl.allput(TreeCommit.rounds_spec(f, cs, ready, ps)) == True{} : Bool}:
  match f:
    case 0n:
      tdl.unknowns(ps)
    case 1n+g:
      +p = TreeCommit.pass(ps, cs, ready)
      tdl.pick(p, TreeCommit.rounds_spec(g, cs, TreeCommit.Pass.ready(p), TreeCommit.Pass.waiting(p)), tdl.rounds(g, cs, TreeCommit.Pass.ready(p), TreeCommit.Pass.waiting(p)))

# Puts' results before ys are skipped
def tdl.skip(xs: List<&2, Tc.Res>, -ys: List<&2, Tc.Res>, h: {tdl.allput(xs) == True{} : Bool}) -> {TreeCommit.after_puts(List.append(&2, Tc.Res, xs, ys)) == TreeCommit.after_puts(ys) : List<&2, Tc.Res>}:
  match xs:
    case Nil{}:
      {==}
    case r <> t:
      match r:
        case Tc.Apply{i}:
          tdl.skip(t, ys, h)
        case Tc.Orphan{i}:
          tdl.skip(t, ys, h)
        case Tc.Retire{i}:
          LATreeCommit.tc.absurd({TreeCommit.after_puts(List.append(&2, Tc.Res, Tc.Retire{i} <> t, ys)) == TreeCommit.after_puts(ys) : List<&2, Tc.Res>}, h)

# the Dels start with a Del, or are none
def tdl.dels(cs: List<&2, Tc.Ch>, +i: Nat) -> {TreeCommit.after_puts(TreeCommit.dels_spec(cs, i)) == TreeCommit.dels_spec(cs, i) : List<&2, Tc.Res>}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case Tc.Here{k}:
          tdl.dels(t, 1n+i)
        case Tc.Under{k, u}:
          tdl.dels(t, 1n+i)
        case Tc.Gone{}:
          {==}

def TreeCommit.tree_commit_dels_last(cs):
  %Equal.sym(List<&2, Tc.Res>, Tc.order(cs), TreeCommit.order_spec(cs), TreeCommit.tree_commit_order_exact(cs)) : {TreeCommit.after_puts(_) == TreeCommit.dels_spec(cs, 0n) : List<&2, Tc.Res>}
  +R = TreeCommit.rounds_spec(List.length(&2, Tc.Ch, cs), cs, [], TreeCommit.put_indices(cs, 0n))
  Equal.trans(List<&2, Tc.Res>, TreeCommit.after_puts(List.append(&2, Tc.Res, R, TreeCommit.dels_spec(cs, 0n))), TreeCommit.after_puts(TreeCommit.dels_spec(cs, 0n)), TreeCommit.dels_spec(cs, 0n), tdl.skip(R, TreeCommit.dels_spec(cs, 0n), tdl.rounds(List.length(&2, Tc.Ch, cs), cs, [], TreeCommit.put_indices(cs, 0n))), tdl.dels(cs, 0n))
