# eukhe: the proof of LAW tree_commit_once

import Base
import ../../bend/tree_commit.bend as Tc
import ../../bend/ffi_tree_commit.bend as FTc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/tree_commit.bend as TreeCommit
import ./base.bend as LATreeCommit
import ./tree_commit_order_exact.bend as PTreeCommitOrderExact

# PROOF of LAW tree_commit_once: the order is the spec's (tree_commit_order_exact); a pass keeps every waiting Put's count, applied or still waiting (tco.pass); the rounds answer each waiting Put as often as it waits (tco.rounds); the Dels answer no Put (tco.dels).

def tco.add_succ(x: Nat, +y: Nat) -> {Nat.add(x, 1n+y) == 1n+Nat.add(x, y) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+z:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(z, 1n+y), 1n+Nat.add(z, y), tco.add_succ(z, y))

def tco.add_zero(x: Nat) -> {Nat.add(x, 0n) == x : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+z:
      Equal.cong(Nat, Nat, n => 1n+n, Nat.add(z, 0n), z, tco.add_zero(z))

def tco.one_left(h: Bool, -x: Nat, -y: Nat) -> {Nat.add(TreeCommit.answers.one(h, x), y) == TreeCommit.answers.one(h, Nat.add(x, y)) : Nat}:
  match h:
    case True{}:
      {==}
    case False{}:
      {==}

def tco.one_right(h: Bool, +x: Nat, +y: Nat) -> {Nat.add(x, TreeCommit.answers.one(h, y)) == TreeCommit.answers.one(h, Nat.add(x, y)) : Nat}:
  match h:
    case True{}:
      tco.add_succ(x, y)
    case False{}:
      {==}

# the answers of xs then ys
def tco.app(+i: Nat, xs: List<&2, Tc.Res>, -ys: List<&2, Tc.Res>) -> {TreeCommit.answers(i, List.append(&2, Tc.Res, xs, ys)) == Nat.add(TreeCommit.answers(i, xs), TreeCommit.answers(i, ys)) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case r <> t:
      match r:
        case Tc.Apply{+j}:
          Equal.trans(Nat, TreeCommit.answers.one(Nat.is_eq(j, i), TreeCommit.answers(i, List.append(&2, Tc.Res, t, ys))), TreeCommit.answers.one(Nat.is_eq(j, i), Nat.add(TreeCommit.answers(i, t), TreeCommit.answers(i, ys))), Nat.add(TreeCommit.answers.one(Nat.is_eq(j, i), TreeCommit.answers(i, t)), TreeCommit.answers(i, ys)), Equal.cong(Nat, Nat, n => TreeCommit.answers.one(Nat.is_eq(j, i), n), TreeCommit.answers(i, List.append(&2, Tc.Res, t, ys)), Nat.add(TreeCommit.answers(i, t), TreeCommit.answers(i, ys)), tco.app(i, t, ys)), Equal.sym(Nat, Nat.add(TreeCommit.answers.one(Nat.is_eq(j, i), TreeCommit.answers(i, t)), TreeCommit.answers(i, ys)), TreeCommit.answers.one(Nat.is_eq(j, i), Nat.add(TreeCommit.answers(i, t), TreeCommit.answers(i, ys))), tco.one_left(Nat.is_eq(j, i), TreeCommit.answers(i, t), TreeCommit.answers(i, ys))))
        case Tc.Orphan{+j}:
          Equal.trans(Nat, TreeCommit.answers.one(Nat.is_eq(j, i), TreeCommit.answers(i, List.append(&2, Tc.Res, t, ys))), TreeCommit.answers.one(Nat.is_eq(j, i), Nat.add(TreeCommit.answers(i, t), TreeCommit.answers(i, ys))), Nat.add(TreeCommit.answers.one(Nat.is_eq(j, i), TreeCommit.answers(i, t)), TreeCommit.answers(i, ys)), Equal.cong(Nat, Nat, n => TreeCommit.answers.one(Nat.is_eq(j, i), n), TreeCommit.answers(i, List.append(&2, Tc.Res, t, ys)), Nat.add(TreeCommit.answers(i, t), TreeCommit.answers(i, ys)), tco.app(i, t, ys)), Equal.sym(Nat, Nat.add(TreeCommit.answers.one(Nat.is_eq(j, i), TreeCommit.answers(i, t)), TreeCommit.answers(i, ys)), TreeCommit.answers.one(Nat.is_eq(j, i), Nat.add(TreeCommit.answers(i, t), TreeCommit.answers(i, ys))), tco.one_left(Nat.is_eq(j, i), TreeCommit.answers(i, t), TreeCommit.answers(i, ys))))
        case Tc.Retire{j}:
          tco.app(i, t, ys)

def tco.unknowns(+i: Nat, ps: List<&2, Nat>) -> {TreeCommit.answers(i, TreeCommit.unknowns(ps)) == TreeCommit.count(i, ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case +p <> t:
      Equal.cong(Nat, Nat, n => TreeCommit.answers.one(Nat.is_eq(p, i), n), TreeCommit.answers(i, TreeCommit.unknowns(t)), TreeCommit.count(i, t), tco.unknowns(i, t))

def tco.applies(+i: Nat, ps: List<&2, Nat>) -> {TreeCommit.answers(i, TreeCommit.applies(ps)) == TreeCommit.count(i, ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case +p <> t:
      Equal.cong(Nat, Nat, n => TreeCommit.answers.one(Nat.is_eq(p, i), n), TreeCommit.answers(i, TreeCommit.applies(t)), TreeCommit.count(i, t), tco.applies(i, t))

# the Dels answer no Put
def tco.dels(+i: Nat, cs: List<&2, Tc.Ch>, +k: Nat) -> {TreeCommit.answers(i, TreeCommit.dels_spec(cs, k)) == 0n : Nat}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case Tc.Here{x}:
          tco.dels(i, t, 1n+k)
        case Tc.Under{x, y}:
          tco.dels(i, t, 1n+k)
        case Tc.Gone{}:
          tco.dels(i, t, 1n+k)

def tco.cnt(+i: Nat, p: TreeCommit.Pass) -> Nat:
  match p:
    case TreeCommit.Pass{a, w, rd}:
      Nat.add(TreeCommit.count(i, a), TreeCommit.count(i, w))

# one waiting Put more: applied or waiting
def tco.cons(+i: Nat, b: Bool, +j: Nat, p: TreeCommit.Pass) -> {tco.cnt(i, TreeCommit.pass.cons(b, j, p)) == TreeCommit.answers.one(Nat.is_eq(j, i), tco.cnt(i, p)) : Nat}:
  match b:
    case True{}:
      match p:
        case TreeCommit.Pass{a, w, rd}:
          tco.one_left(Nat.is_eq(j, i), TreeCommit.count(i, a), TreeCommit.count(i, w))
    case False{}:
      match p:
        case TreeCommit.Pass{a, w, rd}:
          tco.one_right(Nat.is_eq(j, i), TreeCommit.count(i, a), TreeCommit.count(i, w))

# a pass keeps every waiting Put's count: applied or still waiting
def tco.pass(ps: List<&2, Nat>, +i: Nat, +cs: List<&2, Tc.Ch>, +ready: List<&2, Nat>) -> {tco.cnt(i, TreeCommit.pass(ps, cs, ready)) == TreeCommit.count(i, ps) : Nat}:
  match ps:
    case Nil{}:
      {==}
    case +j <> +t:
      +c = TreeCommit.at(cs, j)
      +b = TreeCommit.parent_in(ready, c)
      +r = TreeCommit.add_if(b, TreeCommit.key_of(c), ready)
      Equal.trans(Nat, tco.cnt(i, TreeCommit.pass.cons(b, j, TreeCommit.pass(t, cs, r))), TreeCommit.answers.one(Nat.is_eq(j, i), tco.cnt(i, TreeCommit.pass(t, cs, r))), TreeCommit.answers.one(Nat.is_eq(j, i), TreeCommit.count(i, t)), tco.cons(i, b, j, TreeCommit.pass(t, cs, r)), Equal.cong(Nat, Nat, n => TreeCommit.answers.one(Nat.is_eq(j, i), n), tco.cnt(i, TreeCommit.pass(t, cs, r)), TreeCommit.count(i, t), tco.pass(t, i, cs, r)))

def tco.pick(+i: Nat, p: TreeCommit.Pass, -ps: List<&2, Nat>, +rs: List<&2, Tc.Res>, hp: {tco.cnt(i, p) == TreeCommit.count(i, ps) : Nat}, ih: {TreeCommit.answers(i, rs) == TreeCommit.count(i, TreeCommit.Pass.waiting(p)) : Nat}) -> {TreeCommit.answers(i, TreeCommit.rounds.pick(TreeCommit.Pass.applied(p), TreeCommit.Pass.waiting(p), rs)) == TreeCommit.count(i, ps) : Nat}:
  match p:
    case TreeCommit.Pass{a, +w, rd}:
      match a:
        case Nil{}:
          Equal.trans(Nat, TreeCommit.answers(i, TreeCommit.unknowns(w)), TreeCommit.count(i, w), TreeCommit.count(i, ps), tco.unknowns(i, w), hp)
        case +x <> +y:
          %Equal.sym(Nat, TreeCommit.answers(i, List.append(&2, Tc.Res, TreeCommit.applies(x <> y), rs)), Nat.add(TreeCommit.answers(i, TreeCommit.applies(x <> y)), TreeCommit.answers(i, rs)), tco.app(i, TreeCommit.applies(x <> y), rs)) : {_ == TreeCommit.count(i, ps) : Nat}
          %Equal.sym(Nat, TreeCommit.answers(i, TreeCommit.applies(x <> y)), TreeCommit.count(i, x <> y), tco.applies(i, x <> y)) : {Nat.add(_, TreeCommit.answers(i, rs)) == TreeCommit.count(i, ps) : Nat}
          %Equal.sym(Nat, TreeCommit.answers(i, rs), TreeCommit.count(i, w), ih) : {Nat.add(TreeCommit.count(i, x <> y), _) == TreeCommit.count(i, ps) : Nat}
          hp

# the rounds answer each waiting Put as often as it waits
def tco.rounds(f: Nat, +i: Nat, +cs: List<&2, Tc.Ch>, +ready: List<&2, Nat>, +ps: List<&2, Nat>) -> {TreeCommit.answers(i, TreeCommit.rounds_spec(f, cs, ready, ps)) == TreeCommit.count(i, ps) : Nat}:
  match f:
    case 0n:
      tco.unknowns(i, ps)
    case 1n++g:
      +p = TreeCommit.pass(ps, cs, ready)
      tco.pick(i, p, ps, TreeCommit.rounds_spec(g, cs, TreeCommit.Pass.ready(p), TreeCommit.Pass.waiting(p)), tco.pass(ps, i, cs, ready), tco.rounds(g, i, cs, TreeCommit.Pass.ready(p), TreeCommit.Pass.waiting(p)))

def TreeCommit.tree_commit_once(cs, i):
  %Equal.sym(List<&2, Tc.Res>, Tc.order(cs), TreeCommit.order_spec(cs), TreeCommit.tree_commit_order_exact(cs)) : {TreeCommit.answers(i, _) == TreeCommit.count(i, TreeCommit.put_indices(cs, 0n)) : Nat}
  +R = TreeCommit.rounds_spec(List.length(&2, Tc.Ch, cs), cs, [], TreeCommit.put_indices(cs, 0n))
  %Equal.sym(Nat, TreeCommit.answers(i, List.append(&2, Tc.Res, R, TreeCommit.dels_spec(cs, 0n))), Nat.add(TreeCommit.answers(i, R), TreeCommit.answers(i, TreeCommit.dels_spec(cs, 0n))), tco.app(i, R, TreeCommit.dels_spec(cs, 0n))) : {_ == TreeCommit.count(i, TreeCommit.put_indices(cs, 0n)) : Nat}
  %Equal.sym(Nat, TreeCommit.answers(i, TreeCommit.dels_spec(cs, 0n)), 0n, tco.dels(i, cs, 0n)) : {Nat.add(TreeCommit.answers(i, R), _) == TreeCommit.count(i, TreeCommit.put_indices(cs, 0n)) : Nat}
  %Equal.sym(Nat, Nat.add(TreeCommit.answers(i, R), 0n), TreeCommit.answers(i, R), tco.add_zero(TreeCommit.answers(i, R))) : {_ == TreeCommit.count(i, TreeCommit.put_indices(cs, 0n)) : Nat}
  tco.rounds(List.length(&2, Tc.Ch, cs), i, cs, [], TreeCommit.put_indices(cs, 0n))
