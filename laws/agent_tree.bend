# eukhe: the laws of area agent_tree

import Base
import ../bend/agent_tree.bend as T
import ../spec/agents/agent_tree.bend as S

# (T1-T11) The binary agent tree
# ------------------------------
# bend/agent_tree.bend: the decisions of a tree of agents, each node a
# leaf that works alone or a split into exactly two children. The spec
# spec/agents/agent_tree.bend states T1-T11 and the helpers (scopes as
# counts, node_at and put by path, quiet, room, spent_all, restrict,
# apply_seq). Every input is free: any tree, path, scope, patch, budget,
# deadline, bounds and event list; "reachable" is any tree run(evs, b,
# init(s, lim, dl)) for any events evs. Lim covers Unlimited (the default
# run) and every value.

# Spec helpers
# ------------

# the tree a step leaves: the new one, or the old one when refused
def landed(s: T.Step, t: T.Node) -> T.Node:
  match s:
    case T.Took{n}:
      n
    case T.Refused{why}:
      t

def is_leaf(n: T.Node) -> Bool:
  match n:
    case T.Leaf{i}:
      True{}
    case T.Split{i, own, l, r}:
      False{}

# the first refusal whose check failed, in order; none failed: None
type Check is Data:
  Check{ok: Bool, why: T.Refusal}

def first_failed(cs: List<&2, Check>) -> Maybe<&2, T.Refusal>:
  match cs:
    case Nil{}:
      None{}
    case Con{c, t}:
      match c:
        case Check{ok, why}:
          match ok:
            case True{}:
              first_failed(t)
            case False{}:
              Some{why}

# the step a decision gives: the refusal, else the new tree
def decided(m: Maybe<&2, T.Refusal>, n: T.Node) -> T.Step:
  match m:
    case None{}:
      T.Took{n}
    case Some{why}:
      T.Refused{why}

def info_with(i: T.Info, st: T.Status, lim: T.Lim, sp: Nat, p: List<&2, Maybe<&2, Nat>>) -> T.Info:
  match i:
    case T.Info{a, s, b, c, dl, q}:
      T.Info{st, s, lim, sp, dl, p}

def new_leaf(s: List<&2, Bool>, lim: T.Lim, dl: T.Lim) -> T.Node:
  T.Leaf{T.Info{T.Running{}, s, lim, 0n, dl, []}}

# T1: the node n at depth d of t split into own, ls and rs with the hold
# kept: the checks in order, and the split node (each child running, its
# limit a half of the room less the hold, the deadline less the margin)
def split_checks(+b: T.Bounds, +t: T.Node, +d: Nat, +n: T.Node, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat) -> List<&2, Check>:
  [Check{S.is_running(n), T.NotRunning{}}, Check{is_leaf(n), T.NotLeaf{}}, Check{Nat.is_le(1n+d, T.bound_depth(b)), T.TooDeep{}}, Check{Nat.is_le(Nat.add(S.nodes(t), 2n), T.bound_nodes(b)), T.TooMany{}}, Check{Bool.and(S.splits(T.scope_of(T.info(n)), own, ls, rs), Bool.and(S.owns_some(ls), S.owns_some(rs))), T.BadScopes{}}, Check{S.has(Nat.add(hold, 2n), S.room(n)), T.NoBudget{}}]

def split_node(+b: T.Bounds, +n: T.Node, own: List<&2, Bool>, ls: List<&2, Bool>, rs: List<&2, Bool>, +hold: Nat) -> T.Node:
  +c = S.minus(S.room(n), hold)
  +dl = S.minus(T.deadline_of(T.info(n)), T.bound_margin(b))
  T.Split{T.info(n), own, new_leaf(ls, T.half_hi(c), dl), new_leaf(rs, T.half_lo(c), dl)}

def split_spec_at(m: Maybe<&2, T.Node>, +b: T.Bounds, +t: T.Node, +p: List<&2, T.Dir>, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, +hold: Nat) -> T.Step:
  match m:
    case None{}:
      T.Refused{T.NoNode{}}
    case Some{+n}:
      decided(first_failed(split_checks(b, t, S.length(p), n, own, ls, rs, hold)), S.put(p, t, split_node(b, n, own, ls, rs, hold)))

def split_spec(+b: T.Bounds, +t: T.Node, +p: List<&2, T.Dir>, own: List<&2, Bool>, ls: List<&2, Bool>, rs: List<&2, Bool>, hold: Nat) -> T.Step:
  split_spec_at(S.node_at(p, t), b, t, p, own, ls, rs, hold)

# T1, T8: the halves of c are fair: they add up to c and differ by at
# most one, the larger first
def fair(+c: Nat, hi: T.Lim, lo: T.Lim) -> Bool:
  match hi lo:
    case T.Unlimited{} T.Unlimited{}:
      False{}
    case T.Unlimited{} T.Value{y}:
      False{}
    case T.Value{x} T.Unlimited{}:
      False{}
    case T.Value{+x} T.Value{+y}:
      Bool.and(Nat.is_eq(Nat.add(x, y), c), Bool.or(Nat.is_eq(x, y), Nat.is_eq(x, 1n+y)))

def is_unlimited(l: T.Lim) -> Bool:
  match l:
    case T.Unlimited{}:
      True{}
    case T.Value{n}:
      False{}

# a leaf, or a split whose children both settled
def settled_below(n: T.Node) -> Bool:
  match n:
    case T.Leaf{i}:
      True{}
    case T.Split{i, own, l, r}:
      Bool.and(Bool.not(S.is_running(l)), Bool.not(S.is_running(r)))
# T6: finishing the node at p with the patch q
def finish_checks(+n: T.Node) -> List<&2, Check>:
  [Check{S.is_running(n), T.NotRunning{}}, Check{settled_below(n), T.Unsettled{}}]


def with_info(n: T.Node, j: T.Info) -> T.Node:
  match n:
    case T.Leaf{i}:
      T.Leaf{j}
    case T.Split{i, own, l, r}:
      T.Split{j, own, l, r}

def finish_spec_at(m: Maybe<&2, T.Node>, +t: T.Node, +p: List<&2, T.Dir>, q: List<&2, Maybe<&2, Nat>>) -> T.Step:
  match m:
    case None{}:
      T.Refused{T.NoNode{}}
    case Some{+n}:
      +i = T.info(n)
      decided(first_failed(finish_checks(n)), S.put(p, t, with_info(n, info_with(i, T.Finished{}, T.limit_of(i), T.spent_of(i), q))))

def finish_spec(+t: T.Node, +p: List<&2, T.Dir>, q: List<&2, Maybe<&2, Nat>>) -> T.Step:
  finish_spec_at(S.node_at(p, t), t, p, q)

# T8: spending a at the node at p
def spend_spec_at(m: Maybe<&2, T.Node>, +t: T.Node, +p: List<&2, T.Dir>, +a: Nat) -> T.Step:
  match m:
    case None{}:
      T.Refused{T.NoNode{}}
    case Some{+n}:
      +i = T.info(n)
      decided(first_failed([Check{S.is_running(n), T.NotRunning{}}, Check{S.has(a, S.room(n)), T.NoBudget{}}]), S.put(p, t, with_info(n, info_with(i, T.st_of(i), T.limit_of(i), Nat.add(T.spent_of(i), a), T.patch_of(i)))))

def spend_spec(+t: T.Node, +p: List<&2, T.Dir>, a: Nat) -> T.Step:
  spend_spec_at(S.node_at(p, t), t, p, a)

# T11: redoing the child on side of the node at p with the extra x
def side_of(d: T.Dir, l: T.Node, r: T.Node) -> T.Node:
  match d:
    case T.GoL{}:
      l
    case T.GoR{}:
      r

def fc_status(st: T.Status) -> Bool:
  match st:
    case T.Running{}:
      False{}
    case T.Finished{}:
      False{}
    case T.Failed{}:
      True{}
    case T.Cancelled{}:
      True{}

def failed_or_cancelled_leaf(c: T.Node) -> Bool:
  match c:
    case T.Leaf{i}:
      fc_status(T.st_of(i))
    case T.Split{i, own, l, r}:
      False{}

def redone_with(c: T.Node, lim: T.Lim) -> T.Node:
  match c:
    case T.Leaf{+i}:
      T.Leaf{info_with(i, T.Running{}, lim, T.spent_of(i), T.patch_of(i))}
    case T.Split{i, own, l, r}:
      T.Split{i, own, l, r}

def redone_plus(c: T.Node, x: Nat) -> T.Node:
  match c:
    case T.Leaf{+i}:
      T.Leaf{info_with(i, T.Running{}, T.Value{Nat.add(T.spent_of(i), x)}, T.spent_of(i), T.patch_of(i))}
    case T.Split{i, own, l, r}:
      T.Split{i, own, l, r}

# the redone child: running, its limit what it spent plus x (Unlimited
# when the parent's room is)
def regranted(room: T.Lim, c: T.Node, x: Nat) -> T.Node:
  match room:
    case T.Unlimited{}:
      redone_with(c, T.Unlimited{})
    case T.Value{m}:
      redone_plus(c, x)

def redo_node(d: T.Dir, n: T.Node, +x: Nat) -> Maybe<&2, T.Node>:
  match d:
    case T.GoL{}:
      match n:
        case T.Leaf{i}:
          None{}
        case T.Split{+i, +own, +l, +r}:
          Some{T.Split{i, own, regranted(S.room(T.Split{i, own, l, r}), l, x), r}}
    case T.GoR{}:
      match n:
        case T.Leaf{i}:
          None{}
        case T.Split{+i, +own, +l, +r}:
          Some{T.Split{i, own, l, regranted(S.room(T.Split{i, own, l, r}), r, x)}}

def redo_target(n: T.Node, d: T.Dir) -> Bool:
  match n:
    case T.Leaf{i}:
      False{}
    case T.Split{i, own, l, r}:
      failed_or_cancelled_leaf(side_of(d, l, r))

def redo_checks(+n: T.Node, +d: T.Dir, +x: Nat) -> List<&2, Check>:
  [Check{S.is_running(n), T.NotRunning{}}, Check{redo_target(n, d), T.NotRedoable{}}, Check{S.has(x, S.room(n)), T.NoBudget{}}]

def or_same(m: Maybe<&2, T.Node>, n: T.Node) -> T.Node:
  match m:
    case None{}:
      n
    case Some{k}:
      k

def redo_spec_at(m: Maybe<&2, T.Node>, +t: T.Node, +p: List<&2, T.Dir>, +d: T.Dir, +x: Nat) -> T.Step:
  match m:
    case None{}:
      T.Refused{T.NoNode{}}
    case Some{+n}:
      decided(first_failed(redo_checks(n, d, x)), S.put(p, t, or_same(redo_node(d, n, x), n)))

def redo_spec(+t: T.Node, +p: List<&2, T.Dir>, d: T.Dir, x: Nat) -> T.Step:
  redo_spec_at(S.node_at(p, t), t, p, d, x)

def quiet_of(m: Maybe<&2, T.Node>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{n}:
      S.quiet(n)
# T7: the subtree at p runs nothing (no node at p: false)
def quiet_at(p: List<&2, T.Dir>, t: T.Node) -> Bool:
  quiet_of(S.node_at(p, t))


def is_failed(st: T.Status) -> Bool:
  match st:
    case T.Running{}:
      False{}
    case T.Finished{}:
      False{}
    case T.Failed{}:
      True{}
    case T.Cancelled{}:
      False{}

def write_is(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case None{} Some{y}:
      False{}
    case Some{x} None{}:
      False{}
    case Some{x} Some{y}:
      Nat.is_eq(x, y)

def patch_is(a: List<&2, Maybe<&2, Nat>>, b: List<&2, Maybe<&2, Nat>>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, yt}:
      False{}
    case Con{x, xt} Nil{}:
      False{}
    case Con{x, xt} Con{y, yt}:
      Bool.and(write_is(x, y), patch_is(xt, yt))

# T7: the node at p failed with the patch q, the rest of its subtree quiet
def failed_with(m: Maybe<&2, T.Node>, q: List<&2, Maybe<&2, Nat>>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{n}:
      match n:
        case T.Leaf{+i}:
          Bool.and(is_failed(T.st_of(i)), patch_is(T.patch_of(i), q))
        case T.Split{+i, own, l, r}:
          Bool.and(Bool.and(is_failed(T.st_of(i)), patch_is(T.patch_of(i), q)), Bool.and(S.quiet(l), S.quiet(r)))

# T10
def is_waits(a: T.Action) -> Bool:
  match a:
    case T.ReadMessage{}:
      False{}
    case T.Integrate{}:
      False{}
    case T.WorkOwn{}:
      False{}
    case T.Waits{}:
      True{}

# nothing to do: no message, no arrived result, no own work
def idle(v: T.View) -> Bool:
  match v:
    case T.View{m, n, w}:
      Bool.and(Bool.not(m), Bool.and(Nat.is_eq(n, 0n), Bool.not(w)))

# Laws: split (T1)
# ----------------

# LAW agent_tree_split_is_spec (T1): a split at the path p of any tree t
# is refused NoNode when no node is at p, else refused with the first of
# NotRunning, NotLeaf, TooDeep (depth + 1 past max_depth), TooMany (nodes
# + 2 past max_nodes), BadScopes (own, ls, rs not splitting the node's
# scope unit by unit, or a child owning no unit), NoBudget (the node's
# room below hold + 2) that fails; else the node becomes a split with its
# info and own, and two running leaves over ls and rs, nothing spent, the
# halves (T.half_hi, T.half_lo) of room - hold as limits, deadline less the
# margin; nothing else of the tree changes
# EXCLUDES: a split of a running split; children over overlapping or
#   missing units; a third check skipped; children given the parent's
#   whole room; the hold not kept; a child's deadline past the parent's
law agent_tree_split_is_spec:
  for +b: T.Bounds
  for +t: T.Node
  for +p: List<&2, T.Dir>
  for +own: List<&2, Bool>
  for +ls: List<&2, Bool>
  for +rs: List<&2, Bool>
  for +hold: Nat
  {T.step(b, t, T.EvSplit{p, own, ls, rs, hold}) == split_spec(b, t, p, own, ls, rs, hold) : T.Step}

# LAW agent_tree_halves_fair (T1, T8): for every amount c, the two halves
# a split gives are values that add up to c and differ by at most one,
# the larger to the left child
# EXCLUDES: halves that lose a unit of an odd amount; the whole amount to
#   one child; the larger half to the right
law agent_tree_halves_fair:
  for +c: Nat
  {fair(c, T.half_hi(T.Value{c}), T.half_lo(T.Value{c})) == True{} : Bool}

# LAW agent_tree_halves_unlimited (T1, T8): the halves of Unlimited are
# Unlimited (the default run gives each child no limit)
# EXCLUDES: a zero or one-unit limit for children of an unlimited parent
law agent_tree_halves_unlimited:
  {Bool.and(is_unlimited(T.half_hi(T.Unlimited{})), is_unlimited(T.half_lo(T.Unlimited{}))) == True{} : Bool}

# Laws: partition (T2)
# --------------------

# LAW agent_tree_tiles_root (T2): in every tree reachable from the root
# over the scope s, the own scopes of the splits and the scopes of the
# leaves own each unit exactly as often as s does
# EXCLUDES: a split whose children overlap; a split that drops a unit of
#   its scope; a redo that widens a child's scope
law agent_tree_tiles_root:
  for evs: List<&2, T.Ev>
  for +b: T.Bounds
  for +s: List<&2, Bool>
  for lim: T.Lim
  for dl: T.Lim
  {S.tile(T.run(evs, b, T.init(s, lim, dl))) == S.counts(s) : List<&2, Nat>}

# Laws: integration (T3, T4, T5)
# ------------------------------

# LAW agent_tree_overlay_applies (T3): for every files f, parent patch c,
# child patch a and child scope s, the files with the integrated patch
# are the files with c and then a's writes inside s
# EXCLUDES: a write outside the scope applied; a write inside dropped;
#   the parent's write winning over the child's inside the child's scope
law agent_tree_overlay_applies:
  for +f: List<&2, Nat>
  for c: List<&2, Maybe<&2, Nat>>
  for +a: List<&2, Maybe<&2, Nat>>
  for +s: List<&2, Bool>
  {T.apply(f, T.overlay(c, a, s)) == T.apply(T.apply(f, c), S.restrict(a, s)) : List<&2, Nat>}

# LAW agent_tree_conflicts_cover (T3): every unit the child wrote is
# either applied (inside its scope) or reported as a conflict, and only
# those units are reported
# EXCLUDES: conflicts never reported; a conflict reported for a unit the
#   child did not write
law agent_tree_conflicts_cover:
  for +a: List<&2, Maybe<&2, Nat>>
  for +s: List<&2, Bool>
  {S.or_mask(S.writes(S.restrict(a, s)), T.conflicts(a, s)) == S.writes(a) : List<&2, Bool>}

# LAW agent_tree_conflicts_outside (T3): a reported conflict is never a
# unit of the child's scope
# EXCLUDES: every write reported as a conflict
law agent_tree_conflicts_outside:
  for +a: List<&2, Maybe<&2, Nat>>
  for +s: List<&2, Bool>
  {S.disjoint(T.conflicts(a, s), s) == True{} : Bool}

# LAW agent_tree_arrival_commutes (T4): for two children whose scopes sa,
# sb are disjoint, integrating a then x gives the same files as x then a,
# for every files f and parent patch c
# EXCLUDES: an integration that lets the later child overwrite the earlier
#   one's scope; one that drops the first child's writes
law agent_tree_arrival_commutes:
  for +f: List<&2, Nat>
  for +c: List<&2, Maybe<&2, Nat>>
  for +a: List<&2, Maybe<&2, Nat>>
  for +sa: List<&2, Bool>
  for +x: List<&2, Maybe<&2, Nat>>
  for +sb: List<&2, Bool>
  for e: {S.disjoint(sa, sb) == True{} : Bool}
  {T.apply(f, T.overlay(T.overlay(c, a, sa), x, sb)) == T.apply(f, T.overlay(T.overlay(c, x, sb), a, sa)) : List<&2, Nat>}

# LAW agent_tree_parallel_is_sequential (T5): for every tree whose every
# patch stays in its node's scope and whose splits split their scopes
# (S.tidy), and every files f, the files with the root's integrated
# patch (each child's computed alone from the same base) are the files
# after every node's patch in post-order, one after another
# EXCLUDES: the node's own patch applied before its children's; a child's
#   result integrated under the sibling's scope; the right subtree's
#   result dropped
# WITNESS: a leaf with an empty patch is tidy.
law agent_tree_parallel_is_sequential:
  for +t: T.Node
  for +f: List<&2, Nat>
  for e: {S.tidy(t) == True{} : Bool}
  {T.apply(f, T.result(t)) == S.apply_seq(S.patches(t), f) : List<&2, Nat>}

# Laws: settle (T6)
# -----------------

# LAW agent_tree_finish_is_spec (T6): finishing the node at p with the
# patch q is refused NoNode when no node is there, NotRunning when it
# does not run, Unsettled when it is a split with a running child; else
# the node is Finished with q and nothing else changes
# EXCLUDES: a split finished while a child runs; a settled node finished
#   again; the patch dropped
law agent_tree_finish_is_spec:
  for +b: T.Bounds
  for +t: T.Node
  for +p: List<&2, T.Dir>
  for +q: List<&2, Maybe<&2, Nat>>
  {T.step(b, t, T.EvFinish{p, q}) == finish_spec(t, p, q) : T.Step}

# LAW agent_tree_no_orphan (T6): in every reachable tree, below a node
# that does not run no node runs
# EXCLUDES: a fail that leaves children running; a redo under a settled
#   parent; a tick that cancels a node but not its subtree
law agent_tree_no_orphan:
  for evs: List<&2, T.Ev>
  for +b: T.Bounds
  for s: List<&2, Bool>
  for lim: T.Lim
  for dl: T.Lim
  {S.no_orphan(T.run(evs, b, T.init(s, lim, dl))) == True{} : Bool}

# LAW agent_tree_done_settled (T6): in every reachable tree, every
# finished split has both children settled
# EXCLUDES: a redo of a child under a finished parent
law agent_tree_done_settled:
  for evs: List<&2, T.Ev>
  for +b: T.Bounds
  for s: List<&2, Bool>
  for lim: T.Lim
  for dl: T.Lim
  {S.done_settled(T.run(evs, b, T.init(s, lim, dl))) == True{} : Bool}

# Laws: cancel, fail (T7)
# -----------------------

# LAW agent_tree_cancel_quiets (T7): for every tree t with a node at p,
# after cancelling p no node of p's subtree runs
# EXCLUDES: a cancel of the node alone; a cancel that stops at the first
#   level
# WITNESS: p = [] and n = t meet the premise for every t.
law agent_tree_cancel_quiets:
  for +b: T.Bounds
  for +t: T.Node
  for +p: List<&2, T.Dir>
  for n: T.Node
  for e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}
  {quiet_at(p, landed(T.step(b, t, T.EvCancel{p}), t)) == True{} : Bool}

# LAW agent_tree_cancel_frame (T7): for every tree t with the node n at
# p, a cancel at p changes nothing outside p's subtree: putting n back
# gives t
# EXCLUDES: a cancel that also stops the siblings or the parent
# WITNESS: p = [] and n = t.
law agent_tree_cancel_frame:
  for +b: T.Bounds
  for +t: T.Node
  for +p: List<&2, T.Dir>
  for +n: T.Node
  for e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}
  {S.put(p, landed(T.step(b, t, T.EvCancel{p}), t), n) == t : T.Node}

# LAW agent_tree_fail_quiets (T7): for every tree t with a running node at
# p, after a fail at p with the patch q the node is Failed with q and no
# node below it runs
# EXCLUDES: the partial patch dropped; the children left running; the
#   node marked cancelled
# WITNESS: t = n = init(s, lim, dl), p = [].
law agent_tree_fail_quiets:
  for +b: T.Bounds
  for +t: T.Node
  for +p: List<&2, T.Dir>
  for +q: List<&2, Maybe<&2, Nat>>
  for +n: T.Node
  for e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}
  for r: {S.is_running(n) == True{} : Bool}
  {failed_with(S.node_at(p, landed(T.step(b, t, T.EvFail{p, q}), t)), q) == True{} : Bool}

# LAW agent_tree_fail_frame (T7): a fail at p changes nothing outside p's
# subtree
# EXCLUDES: a fail that also fails the parent
# WITNESS: p = [] and n = t.
law agent_tree_fail_frame:
  for +b: T.Bounds
  for +t: T.Node
  for +p: List<&2, T.Dir>
  for +q: List<&2, Maybe<&2, Nat>>
  for +n: T.Node
  for e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}
  {S.put(p, landed(T.step(b, t, T.EvFail{p, q}), t), n) == t : T.Node}

# LAW agent_tree_fail_needs_running (T7): a fail at a node that does not
# run is refused NotRunning
# EXCLUDES: a finished node turned failed
# WITNESS: t = n a finished leaf, p = [].
law agent_tree_fail_needs_running:
  for +b: T.Bounds
  for +t: T.Node
  for +p: List<&2, T.Dir>
  for +q: List<&2, Maybe<&2, Nat>>
  for +n: T.Node
  for e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}
  for r: {S.is_running(n) == False{} : Bool}
  {T.step(b, t, T.EvFail{p, q}) == T.Refused{T.NotRunning{}} : T.Step}

# Laws: budget, deadline (T8)
# ---------------------------

# LAW agent_tree_spend_is_spec (T8): a spend of a at p is refused NoNode
# when no node is there, NotRunning when it does not run, NoBudget when a
# is past the node's room (limit - own spend - what each child holds: a
# running child its limit, a settled one its subtree's spend); else the
# node's spend grows by a and nothing else changes
# EXCLUDES: a settled child's unspent limit kept from the parent; a spend
#   past the room; a spend charged to the parent
law agent_tree_spend_is_spec:
  for +b: T.Bounds
  for +t: T.Node
  for +p: List<&2, T.Dir>
  for +a: Nat
  {T.step(b, t, T.EvSpend{p, a}) == spend_spec(t, p, a) : T.Step}

# LAW agent_tree_budget_holds (T8): in every tree reachable from a root
# with the limit lim, everything every node spent together fits lim
# EXCLUDES: children given the parent's whole limit without the parent's
#   spend counted; a redo whose extra is not taken from the parent
law agent_tree_budget_holds:
  for evs: List<&2, T.Ev>
  for +b: T.Bounds
  for s: List<&2, Bool>
  for +lim: T.Lim
  for dl: T.Lim
  {S.has(S.spent_all(T.run(evs, b, T.init(s, lim, dl))), lim) == True{} : Bool}

# LAW agent_tree_deadlines_down (T8): in every reachable tree no child's
# deadline is past its parent's
# EXCLUDES: a child's deadline set to the margin past the parent's; an
#   unlimited child under a bounded parent
law agent_tree_deadlines_down:
  for evs: List<&2, T.Ev>
  for +b: T.Bounds
  for s: List<&2, Bool>
  for lim: T.Lim
  for dl: T.Lim
  {S.deadlines_down(T.run(evs, b, T.init(s, lim, dl))) == True{} : Bool}

# LAW agent_tree_tick_none_late (T8): for every tree, after a tick at now
# no running node's deadline is up at now
# EXCLUDES: a tick that checks only the root; a tick that leaves the
#   subtree of a cancelled node running
law agent_tree_tick_none_late:
  for +b: T.Bounds
  for +t: T.Node
  for +now: Nat
  {S.none_late(landed(T.step(b, t, T.EvTick{now}), t), now) == True{} : Bool}

# LAW agent_tree_tick_keeps_on_time (T8): a tick at now changes nothing in
# a tree with no running node late at now (an Unlimited deadline is never
# late)
# EXCLUDES: a tick that cancels an unlimited node; one that cancels a node
#   whose deadline is still ahead
law agent_tree_tick_keeps_on_time:
  for +b: T.Bounds
  for +t: T.Node
  for +now: Nat
  for e: {S.none_late(t, now) == True{} : Bool}
  {T.step(b, t, T.EvTick{now}) == T.Took{t} : T.Step}

# T8: the node n is running with its deadline up at now
def late(+n: T.Node, +now: Nat) -> Bool:
  Bool.and(S.is_running(n), S.up(T.deadline_of(T.info(n)), now))

# T8: no node on the path p from the root of t to its end (both
# included) is late at now
def on_time_path(p: List<&2, T.Dir>, +t: T.Node, +now: Nat) -> Bool:
  match p:
    case Nil{}:
      Bool.not(late(t, now))
    case Con{d, rest}:
      match d:
        case T.GoL{}:
          match t:
            case T.Leaf{+i}:
              Bool.not(late(T.Leaf{i}, now))
            case T.Split{+i, +own, +l, +r}:
              Bool.and(Bool.not(late(T.Split{i, own, l, r}, now)), on_time_path(rest, l, now))
        case T.GoR{}:
          match t:
            case T.Leaf{+i}:
              Bool.not(late(T.Leaf{i}, now))
            case T.Split{+i, +own, +l, +r}:
              Bool.and(Bool.not(late(T.Split{i, own, l, r}, now)), on_time_path(rest, r, now))

# T8: a node is there and runs
def runs_at(m: Maybe<&2, T.Node>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{n}:
      S.is_running(n)

# LAW agent_tree_tick_cancels_only_late (T8): for every tree t and running
# node n at p, when no node on the path from the root to n is late at now,
# n still runs after a tick at now (a tick cancels only late nodes and the
# subtrees below them)
# EXCLUDES: a tick that cancels every running node once any is late; one
#   that cancels a late node's siblings
# WITNESS: t = n = init(s, lim, Unlimited{}), p = [], any now.
law agent_tree_tick_cancels_only_late:
  for +b: T.Bounds
  for +t: T.Node
  for +p: List<&2, T.Dir>
  for +now: Nat
  for +n: T.Node
  for e: {S.node_at(p, t) == Some{n} : Maybe<&2, T.Node>}
  for r: {S.is_running(n) == True{} : Bool}
  for o: {on_time_path(p, t, now) == True{} : Bool}
  {runs_at(S.node_at(p, landed(T.step(b, t, T.EvTick{now}), t))) == True{} : Bool}

# Laws: bounds (T9)
# -----------------

# LAW agent_tree_depth_bound (T9): every reachable tree is at most
# max_depth deep
# EXCLUDES: the depth check off by one; a split of a node at max depth
law agent_tree_depth_bound:
  for evs: List<&2, T.Ev>
  for +b: T.Bounds
  for s: List<&2, Bool>
  for lim: T.Lim
  for dl: T.Lim
  {Nat.is_le(S.depth(T.run(evs, b, T.init(s, lim, dl))), T.bound_depth(b)) == True{} : Bool}

# LAW agent_tree_nodes_bound (T9): with max_nodes at least one, every
# reachable tree has at most max_nodes nodes
# EXCLUDES: the node check counting one child; no node check
law agent_tree_nodes_bound:
  for evs: List<&2, T.Ev>
  for +b: T.Bounds
  for s: List<&2, Bool>
  for lim: T.Lim
  for dl: T.Lim
  for e: {Nat.is_le(1n, T.bound_nodes(b)) == True{} : Bool}
  {Nat.is_le(S.nodes(T.run(evs, b, T.init(s, lim, dl))), T.bound_nodes(b)) == True{} : Bool}

# Laws: never idle (T10)
# ----------------------

# LAW agent_tree_next_waits_iff_idle (T10): a node waits exactly when it
# has no message, no arrived result and no own work
# EXCLUDES: waiting with a result to integrate; never waiting
law agent_tree_next_waits_iff_idle:
  for +v: T.View
  {is_waits(T.next(v)) == idle(v) : Bool}

# LAW agent_tree_next_message_first (T10): a user message is read first,
# whatever else is ready
# EXCLUDES: integrating before reading the user
law agent_tree_next_message_first:
  for n: Nat
  for w: Bool
  {T.next(T.View{True{}, n, w}) == T.ReadMessage{} : T.Action}

# LAW agent_tree_next_integrates_first (T10): with no message and an
# arrived result, the node integrates, whatever own work is left
# EXCLUDES: own work before integration
law agent_tree_next_integrates_first:
  for n: Nat
  for w: Bool
  {T.next(T.View{False{}, 1n+n, w}) == T.Integrate{} : T.Action}

# LAW agent_tree_next_works_own (T10): with no message and no arrived
# result, own work is done
# EXCLUDES: waiting with own work left
law agent_tree_next_works_own:
  {T.next(T.View{False{}, 0n, True{}}) == T.WorkOwn{} : T.Action}

# Laws: redo (T11)
# ----------------

# LAW agent_tree_redo_is_spec (T11): a redo of the child on side d of the
# node at p with the extra x is refused NoNode when no node is there,
# NotRunning when it does not run, NotRedoable when it is a leaf or the
# child is not a failed or cancelled leaf, NoBudget when x is past the
# node's room; else that child runs again with its scope, spend, deadline
# and patch, its limit its spend plus x (Unlimited when the room is), and
# nothing else changes
# EXCLUDES: a finished child redone; a redo under a settled parent; an
#   extra past the parent's room; the child's spend reset to zero
law agent_tree_redo_is_spec:
  for +b: T.Bounds
  for +t: T.Node
  for +p: List<&2, T.Dir>
  for +d: T.Dir
  for +x: Nat
  {T.step(b, t, T.EvRedo{p, d, x}) == redo_spec(t, p, d, x) : T.Step}
