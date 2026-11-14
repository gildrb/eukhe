# agent_tree (spec): the binary agent tree, stated without the tree's code
# (bend/agent_tree.bend). The laws of area agent_tree
# (laws/agent_tree.bend) state T1-T11 of the code with the helpers below.
# A spec: the shipped code never calls it. docs/internals/agent-tree.md
# is the design.
#
# T1:  a node splits only from a running leaf into exactly two children,
#      admitted exactly when own, left and right split its scope unit by
#      unit (each unit of the scope in exactly one of them, no unit outside
#      it), both children own a unit, depth + 1 <= max_depth, nodes + 2 <=
#      max_nodes and its free budget covers its hold plus one per child;
#      the children start running with nothing spent, the halves of (free
#      - hold) as limits and the parent's deadline less the margin;
#      otherwise refused with the first failing reason, the tree unchanged.
# T2:  in every tree reachable from a root by any events, the own scopes
#      of the splits and the scopes of the leaves hold each unit exactly as
#      often as the root's scope.
# T3:  integrating a child's patch applies exactly its writes inside the
#      child's scope, over the parent's patch; every write outside the
#      scope is reported as a conflict and never applied.
# T4:  for two children with disjoint scopes, integrating left then right
#      gives the same files as right then left.
# T5:  for a tree whose every patch stays in its node's scope and whose
#      splits partition their scopes, applying the root's integrated patch
#      gives the files that applying every node's patch one after another
#      in post-order (left subtree, right subtree, then the node) gives.
# T6:  a node finishes only while running, and a split only once both
#      children are settled; in every reachable tree no running node sits
#      under a settled one and every finished split has settled children.
# T7:  after a cancel or a fail of a node no node of its subtree runs and
#      nothing outside it changes; a failed node keeps its partial patch.
# T8:  a spend is admitted exactly when its node runs and the amount fits
#      the node's free (limit - spent - each child's charge: a running
#      child's limit, a settled child's subtree spend, so a settled child's
#      unspent limit returns to its parent); in every reachable tree the
#      whole tree's spend fits the root's limit and no child's deadline is
#      past its parent's; a tick cancels exactly the running nodes whose
#      deadline is up, and the subtrees below them. Unlimited (the default:
#      until finished) fits everything; its halves are Unlimited; no tick
#      cancels an Unlimited deadline.
# T9:  every reachable tree has depth <= max_depth and at most max_nodes
#      nodes (max_nodes >= 1).
# T10: a node's next action is to wait exactly when no user message, no
#      arrived child result and no own work is there; a user message
#      comes first, then integration, then own work.
# T11: a redo restarts a failed or cancelled leaf under a running parent as
#      a running leaf with its scope, spend, deadline and partial patch,
#      its limit what it spent plus an extra that fits the parent's free
#      (Unlimited under an unlimited parent); anything else is refused.

import Base
import ../../bend/agent_tree.bend as T

# Numbers
# -------

def b2n(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# how often each unit is owned
def counts(xs: List<&2, Bool>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      []
    case Con{x, t}:
      b2n(x) <> counts(t)

# unit-by-unit sum; the longer list's tail stays
def addv(a: List<&2, Nat>, b: List<&2, Nat>) -> List<&2, Nat>:
  match a b:
    case Nil{} Nil{}:
      []
    case Nil{} Con{y, yt}:
      y <> yt
    case Con{x, xt} Nil{}:
      x <> xt
    case Con{x, xt} Con{y, yt}:
      Nat.add(x, y) <> addv(xt, yt)

def nats_eq(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      False{}
    case Con{x, xt} Nil{}:
      False{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(Nat.is_eq(x, y), nats_eq(xt, yt))

def sum(xs: List<&2, Nat>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case Con{x, t}:
      Nat.add(x, sum(t))

# a mask owns at least one unit
def owns_some(xs: List<&2, Bool>) -> Bool:
  Bool.not(Nat.is_eq(sum(counts(xs)), 0n))

def same_lengths(+s: List<&2, Bool>, own: List<&2, Bool>, ls: List<&2, Bool>, rs: List<&2, Bool>) -> Bool:
  Bool.and(Nat.is_eq(List.length(&2, Bool, own), List.length(&2, Bool, s)), Bool.and(Nat.is_eq(List.length(&2, Bool, ls), List.length(&2, Bool, s)), Nat.is_eq(List.length(&2, Bool, rs), List.length(&2, Bool, s))))

# own, ls and rs have the scope's length and together own each unit as
# often as the scope does
def splits(+s: List<&2, Bool>, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>) -> Bool:
  Bool.and(same_lengths(s, own, ls, rs), nats_eq(addv(counts(own), addv(counts(ls), counts(rs))), counts(s)))

# Lim: Unlimited above every value
# -------------------------------

# n fits within l
def has(n: Nat, l: T.Lim) -> Bool:
  match l:
    case T.Unlimited{}:
      True{}
    case T.Value{m}:
      Nat.is_le(n, m)

# a <= b
def lim_le(a: T.Lim, b: T.Lim) -> Bool:
  match a b:
    case T.Unlimited{} T.Unlimited{}:
      True{}
    case T.Unlimited{} T.Value{y}:
      False{}
    case T.Value{x} T.Unlimited{}:
      True{}
    case T.Value{x} T.Value{y}:
      Nat.is_le(x, y)

# l - n, floor 0
def minus(l: T.Lim, n: Nat) -> T.Lim:
  match l:
    case T.Unlimited{}:
      T.Unlimited{}
    case T.Value{m}:
      T.Value{Nat.sub(m, n)}

# a - b, floor 0 (Unlimited - anything: Unlimited; a value - Unlimited: 0)
def minus_lim(a: T.Lim, b: T.Lim) -> T.Lim:
  match a b:
    case T.Unlimited{} T.Unlimited{}:
      T.Unlimited{}
    case T.Unlimited{} T.Value{y}:
      T.Unlimited{}
    case T.Value{x} T.Unlimited{}:
      T.Value{0n}
    case T.Value{x} T.Value{y}:
      T.Value{Nat.sub(x, y)}

# Trees
# -----

def is_running(n: T.Node) -> Bool:
  T.running(T.st_of(T.info(n)))

# the node a path names
def node_at(p: List<&2, T.Dir>, t: T.Node) -> Maybe<&2, T.Node>:
  match p:
    case Nil{}:
      Some{t}
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              None{}
            case T.Split{i, own, l, r}:
              node_at(rest, l)
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              None{}
            case T.Split{i, own, l, r}:
              node_at(rest, r)

# t with the node at p replaced by n (no such node: t)
def put(p: List<&2, T.Dir>, t: T.Node, n: T.Node) -> T.Node:
  match p:
    case Nil{}:
      n
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              T.Leaf{i}
            case T.Split{i, own, l, r}:
              T.Split{i, own, put(rest, l, n), r}
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              T.Leaf{i}
            case T.Split{i, own, l, r}:
              T.Split{i, own, l, put(rest, r, n)}

def length(p: List<&2, T.Dir>) -> Nat:
  match p:
    case Nil{}:
      0n
    case Con{d, t}:
      1n+length(t)

# no node of t runs
def quiet(t: T.Node) -> Bool:
  match t:
    case T.Leaf{i}:
      Bool.not(T.running(T.st_of(i)))
    case T.Split{i, own, l, r}:
      Bool.and(Bool.not(T.running(T.st_of(i))), Bool.and(quiet(l), quiet(r)))

# below every node that does not run, nothing runs
def no_orphan(t: T.Node) -> Bool:
  match t:
    case T.Leaf{i}:
      True{}
    case T.Split{+i, own, +l, +r}:
      Bool.and(Bool.or(T.running(T.st_of(i)), Bool.and(quiet(l), quiet(r))), Bool.and(no_orphan(l), no_orphan(r)))

def is_finished(st: T.Status) -> Bool:
  match st:
    case T.Running{}:
      False{}
    case T.Finished{}:
      True{}
    case T.Failed{}:
      False{}
    case T.Cancelled{}:
      False{}

# every finished split has both children settled
def done_settled(t: T.Node) -> Bool:
  match t:
    case T.Leaf{i}:
      True{}
    case T.Split{+i, own, +l, +r}:
      Bool.and(Bool.or(Bool.not(is_finished(T.st_of(i))), Bool.and(Bool.not(is_running(l)), Bool.not(is_running(r)))), Bool.and(done_settled(l), done_settled(r)))

# how often each unit is owned by the own scopes and the leaves of t
def tile(t: T.Node) -> List<&2, Nat>:
  match t:
    case T.Leaf{i}:
      counts(T.scope_of(i))
    case T.Split{i, own, l, r}:
      addv(counts(own), addv(tile(l), tile(r)))

# what every node of t spent
def spent_all(t: T.Node) -> Nat:
  match t:
    case T.Leaf{i}:
      T.spent_of(i)
    case T.Split{i, own, l, r}:
      Nat.add(T.spent_of(i), Nat.add(spent_all(l), spent_all(r)))

def held_if(run: Bool, lim: T.Lim, sp: Nat) -> T.Lim:
  match run:
    case True{}:
      lim
    case False{}:
      T.Value{sp}

# what a child holds of its parent's limit: all of its limit while it
# runs, what its subtree spent once settled
def held(+c: T.Node) -> T.Lim:
  held_if(is_running(c), T.limit_of(T.info(c)), spent_all(c))

# what the node may still spend: its limit less its own spend and what
# its children hold
def room(t: T.Node) -> T.Lim:
  match t:
    case T.Leaf{+i}:
      minus(T.limit_of(i), T.spent_of(i))
    case T.Split{+i, own, +l, +r}:
      minus_lim(minus_lim(minus(T.limit_of(i), T.spent_of(i)), held(l)), held(r))

# no child's deadline is past its parent's
def deadlines_down(t: T.Node) -> Bool:
  match t:
    case T.Leaf{i}:
      True{}
    case T.Split{+i, own, +l, +r}:
      Bool.and(Bool.and(lim_le(T.deadline_of(T.info(l)), T.deadline_of(i)), lim_le(T.deadline_of(T.info(r)), T.deadline_of(i))), Bool.and(deadlines_down(l), deadlines_down(r)))

# the deadline l is up at now
def up(l: T.Lim, now: Nat) -> Bool:
  match l:
    case T.Unlimited{}:
      False{}
    case T.Value{d}:
      Nat.is_le(d, now)

# no running node of t has its deadline up at now
def none_late(t: T.Node, +now: Nat) -> Bool:
  match t:
    case T.Leaf{+i}:
      Bool.not(Bool.and(T.running(T.st_of(i)), up(T.deadline_of(i), now)))
    case T.Split{+i, own, l, r}:
      Bool.and(Bool.not(Bool.and(T.running(T.st_of(i)), up(T.deadline_of(i), now))), Bool.and(none_late(l, now), none_late(r, now)))

def depth(t: T.Node) -> Nat:
  match t:
    case T.Leaf{i}:
      0n
    case T.Split{i, own, l, r}:
      1n+Nat.max(depth(l), depth(r))

def nodes(t: T.Node) -> Nat:
  match t:
    case T.Leaf{i}:
      1n
    case T.Split{i, own, l, r}:
      Nat.add(nodes(l), 1n+nodes(r))

# Patches
# -------

# a's writes inside s; a's length (s reads False past its end)
def restrict(a: List<&2, Maybe<&2, Nat>>, s: List<&2, Bool>) -> List<&2, Maybe<&2, Nat>>:
  match a:
    case Nil{}:
      []
    case Con{x, xt}:
      match s:
        case Nil{}:
          None{} <> restrict(xt, [])
        case Con{b, bt}:
          match b:
            case True{}:
              x <> restrict(xt, bt)
            case False{}:
              None{} <> restrict(xt, bt)

# the units a writes
def writes(a: List<&2, Maybe<&2, Nat>>) -> List<&2, Bool>:
  match a:
    case Nil{}:
      []
    case Con{x, t}:
      Maybe.is_some(&2, Nat, x) <> writes(t)

def or_mask(a: List<&2, Bool>, b: List<&2, Bool>) -> List<&2, Bool>:
  match a b:
    case Nil{} Nil{}:
      []
    case Nil{} Con{y, yt}:
      y <> yt
    case Con{x, xt} Nil{}:
      x <> xt
    case Con{x, xt} Con{y, yt}:
      Bool.or(x, y) <> or_mask(xt, yt)

# no unit in both
def disjoint(a: List<&2, Bool>, b: List<&2, Bool>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      True{}
    case Con{x, xt} Nil{}:
      True{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(Bool.not(Bool.and(x, y)), disjoint(xt, yt))

# the files f after each patch of ps, one after another
def apply_seq(ps: List<&2, List<&2, Maybe<&2, Nat>>>, f: List<&2, Nat>) -> List<&2, Nat>:
  match ps:
    case Nil{}:
      f
    case Con{p, t}:
      apply_seq(t, T.apply(f, p))

# every node's patch, post-order: left subtree, right subtree, the node
def patches(t: T.Node) -> List<&2, List<&2, Maybe<&2, Nat>>>:
  match t:
    case T.Leaf{i}:
      [T.patch_of(i)]
    case T.Split{i, own, l, r}:
      List.append(&2, List<&2, Maybe<&2, Nat>>, patches(l), List.append(&2, List<&2, Maybe<&2, Nat>>, patches(r), [T.patch_of(i)]))

# every write of a is inside s (s reads False past its end)
def within(a: List<&2, Maybe<&2, Nat>>, s: List<&2, Bool>) -> Bool:
  match a:
    case Nil{}:
      True{}
    case Con{x, xt}:
      match s:
        case Nil{}:
          Bool.and(Maybe.is_none(&2, Nat, x), within(xt, []))
        case Con{b, bt}:
          Bool.and(Bool.or(b, Maybe.is_none(&2, Nat, x)), within(xt, bt))

# every node's patch stays in its scope, and every split's own, left and
# right split its scope
def tidy(t: T.Node) -> Bool:
  match t:
    case T.Leaf{+i}:
      within(T.patch_of(i), T.scope_of(i))
    case T.Split{+i, +own, +l, +r}:
      Bool.and(Bool.and(within(T.patch_of(i), T.scope_of(i)), splits(T.scope_of(i), own, T.scope_of(T.info(l)), T.scope_of(T.info(r)))), Bool.and(tidy(l), tidy(r)))
