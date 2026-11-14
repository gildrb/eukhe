# agent_crown (spec): the agent tree with read-only help leaves, stated
# without the crown's code (bend/agent_crown.bend). The laws of area
# agent_crown (laws/agent_crown.bend) state T14 of the code with the
# helpers below. A spec: the shipped code never calls it.
# docs/internals/agent-tree.md (Help leaves) is the design.
#
# T14: writers form the binary tree (T1-T11); a running node may ask a
#      read-only helper (help(task)): an extra leaf with no write scope
#      (integrating its result applies nothing, every write it made is a
#      conflict), admitted exactly when its node runs, the tree's nodes
#      plus the help leaves plus one fit max_nodes and the amount fits the
#      node's free on the view (the tree with each node's spent raised by
#      the charges of the help leaves at its path: a running help leaf its
#      limit, an Unlimited one nothing, a settled one what it spent); it
#      gets that amount as its limit (Unlimited under an Unlimited free)
#      and the node's deadline less the margin. Every tree decision is
#      taken on the view, with max_nodes less the help leaves; the charges
#      are taken off again after it, and every running help leaf whose
#      node no longer runs, or (on a tick) whose own deadline is up, is
#      cancelled. A help leaf spends within its limit and settles (Finished
#      or Failed) only while running; it never blocks its node's settle. In
#      every crown reachable from a root no running help leaf sits at a
#      node that does not run, the nodes plus the help leaves fit
#      max_nodes, and under a Value root limit the tree's spend plus the
#      help leaves' spend fits it. With no help leaf a tree event is the
#      tree's step.

import Base
import ../../bend/agent_tree.bend as T
import ../../bend/agent_crown.bend as A
import ./agent_tree.bend as S

# Help leaves
# -----------

def tree_of(c: A.Crown) -> T.Node:
  match c:
    case A.Crown{t, hs}:
      t

def helps_of(c: A.Crown) -> List<&2, A.Help>:
  match c:
    case A.Crown{t, hs}:
      hs

def is_running_help(h: A.Help) -> Bool:
  match h:
    case A.Help{p, st, lim, sp, dl}:
      T.running(st)

# how many help leaves
def count(hs: List<&2, A.Help>) -> Nat:
  match hs:
    case Nil{}:
      0n
    case Con{h, rest}:
      Nat.add(1n, count(rest))

# what the help leaves spent
def helps_spent(hs: List<&2, A.Help>) -> Nat:
  match hs:
    case Nil{}:
      0n
    case Con{h, rest}:
      match h:
        case A.Help{p, st, lim, sp, dl}:
          Nat.add(sp, helps_spent(rest))

# the help leaf k (none: None)
def nth(hs: List<&2, A.Help>, k: Nat) -> Maybe<&2, A.Help>:
  match hs:
    case Nil{}:
      None{}
    case Con{h, rest}:
      match k:
        case 0n:
          Some{h}
        case 1n+j:
          nth(rest, j)

# hs with the help leaf k replaced by x
def set(hs: List<&2, A.Help>, k: Nat, x: A.Help) -> List<&2, A.Help>:
  match hs:
    case Nil{}:
      []
    case Con{h, rest}:
      match k:
        case 0n:
          x <> rest
        case 1n+j:
          h <> set(rest, j, x)

def dir_is(x: T.Dir, y: T.Dir) -> Bool:
  match x y:
    case T.GoL{} T.GoL{}:
      True{}
    case T.GoL{} T.GoR{}:
      False{}
    case T.GoR{} T.GoL{}:
      False{}
    case T.GoR{} T.GoR{}:
      True{}

def path_is(a: List<&2, T.Dir>, b: List<&2, T.Dir>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      False{}
    case Con{x, xt} Nil{}:
      False{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(dir_is(x, y), path_is(xt, yt))

# The view
# --------

# what a help leaf charges its node: while running its limit (Unlimited:
# nothing), once settled what it spent
def charge_st(st: T.Status, lim: T.Lim, sp: Nat) -> Nat:
  match st:
    case T.Running{}:
      match lim:
        case T.Unlimited{}:
          0n
        case T.Value{n}:
          n
    case T.Finished{}:
      sp
    case T.Failed{}:
      sp
    case T.Cancelled{}:
      sp

def raise_info(i: T.Info, n: Nat) -> T.Info:
  match i:
    case T.Info{st, s, lim, sp, dl, q}:
      T.Info{st, s, lim, Nat.add(sp, n), dl, q}

def lower_info(i: T.Info, n: Nat) -> T.Info:
  match i:
    case T.Info{st, s, lim, sp, dl, q}:
      T.Info{st, s, lim, Nat.sub(sp, n), dl, q}

def raise_root(t: T.Node, n: Nat) -> T.Node:
  match t:
    case T.Leaf{i}:
      T.Leaf{raise_info(i, n)}
    case T.Split{i, own, l, r}:
      T.Split{raise_info(i, n), own, l, r}

def lower_root(t: T.Node, n: Nat) -> T.Node:
  match t:
    case T.Leaf{i}:
      T.Leaf{lower_info(i, n)}
    case T.Split{i, own, l, r}:
      T.Split{lower_info(i, n), own, l, r}

# t with the spent of the node at p raised by n (no such node: t)
def bump(p: List<&2, T.Dir>, t: T.Node, n: Nat) -> T.Node:
  match p:
    case Nil{}:
      raise_root(t, n)
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              T.Leaf{i}
            case T.Split{i, own, l, r}:
              T.Split{i, own, bump(rest, l, n), r}
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              T.Leaf{i}
            case T.Split{i, own, l, r}:
              T.Split{i, own, l, bump(rest, r, n)}

# t with the spent of the node at p lowered by n, floor 0 (no such node: t)
def unbump(p: List<&2, T.Dir>, t: T.Node, n: Nat) -> T.Node:
  match p:
    case Nil{}:
      lower_root(t, n)
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{i}:
              T.Leaf{i}
            case T.Split{i, own, l, r}:
              T.Split{i, own, unbump(rest, l, n), r}
        case T.GoR{}:
          match t:
            case T.Leaf{i}:
              T.Leaf{i}
            case T.Split{i, own, l, r}:
              T.Split{i, own, l, unbump(rest, r, n)}

# the view: each help leaf's charge added at its path
def view_of(t: T.Node, hs: List<&2, A.Help>) -> T.Node:
  match hs:
    case Nil{}:
      t
    case Con{h, rest}:
      match h:
        case A.Help{p, st, lim, sp, dl}:
          bump(p, view_of(t, rest), charge_st(st, lim, sp))

# the same charges taken off again
def unview_of(t: T.Node, hs: List<&2, A.Help>) -> T.Node:
  match hs:
    case Nil{}:
      t
    case Con{h, rest}:
      match h:
        case A.Help{p, st, lim, sp, dl}:
          unbump(p, unview_of(t, rest), charge_st(st, lim, sp))

def view(c: A.Crown) -> T.Node:
  match c:
    case A.Crown{t, hs}:
      view_of(t, hs)

# the tree's bounds with max_nodes less the help leaves (floor 0)
def bounds(b: T.Bounds, c: A.Crown) -> T.Bounds:
  match b:
    case T.Bounds{d, n, m}:
      T.Bounds{d, Nat.sub(n, count(helps_of(c))), m}

# a node is at p and runs
def runs_at(m: Maybe<&2, T.Node>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{n}:
      S.is_running(n)

# Invariants
# ----------

# every running help leaf of hs has its node running in t
def placed_in(+t: T.Node, hs: List<&2, A.Help>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{h, rest}:
      match h:
        case A.Help{p, st, lim, sp, dl}:
          Bool.and(Bool.or(Bool.not(T.running(st)), runs_at(S.node_at(p, t))), placed_in(t, rest))

# every running help leaf's node runs
def helps_placed(c: A.Crown) -> Bool:
  match c:
    case A.Crown{+t, hs}:
      placed_in(t, hs)

# no help leaf at p runs
def none_run_at(+p: List<&2, T.Dir>, hs: List<&2, A.Help>) -> Bool:
  match hs:
    case Nil{}:
      True{}
    case Con{h, rest}:
      match h:
        case A.Help{q, st, lim, sp, dl}:
          Bool.and(Bool.or(Bool.not(path_is(q, p)), Bool.not(T.running(st))), none_run_at(p, rest))

# the tree's spend plus the help leaves' spend
def crown_spent(c: A.Crown) -> Nat:
  match c:
    case A.Crown{t, hs}:
      Nat.add(S.spent_all(t), helps_spent(hs))

# the tree's nodes plus the help leaves
def crown_nodes(c: A.Crown) -> Nat:
  match c:
    case A.Crown{t, hs}:
      Nat.add(S.nodes(t), count(hs))
