# eukhe: the laws of area agent_crown

import Base
import ../bend/agent_tree.bend as T
import ../bend/agent_crown.bend as A
import ../spec/agents/agent_tree.bend as S
import ../spec/agents/agent_crown.bend as CS
import ./agent_tree.bend as AgentTree

# (T14) Help leaves
# -----------------
# bend/agent_crown.bend: the agent tree (bend/agent_tree.bend, T1-T11)
# with read-only help leaves. The spec spec/agents/agent_crown.bend states
# T14 and the helpers (charges, the view and its undoing by path, nth and
# set of a help leaf, the invariants); the checks in order reuse
# AgentTree.Check and AgentTree.first_failed. Every input is free: any
# crown, tree, help leaves, path, amount, bounds and event list;
# "reachable" is any crown crun(evs, b, cinit(s, lim, dl)) for any events
# evs.

# Spec helpers
# ------------

# the step a decision gives: the refusal, else the new crown
def cdecided(m: Maybe<&2, T.Refusal>, c: A.Crown) -> A.CStep:
  match m:
    case None{}:
      A.CTook{c}
    case Some{why}:
      A.CRefused{why}

# the crown a step leaves: the new one, or the old one when refused
def clanded(s: A.CStep, c: A.Crown) -> A.Crown:
  match s:
    case A.CTook{n}:
      n
    case A.CRefused{why}:
      c

def ctook(s: A.CStep) -> Bool:
  match s:
    case A.CTook{n}:
      True{}
    case A.CRefused{why}:
      False{}

def took(s: T.Step) -> Bool:
  match s:
    case T.Took{n}:
      True{}
    case T.Refused{why}:
      False{}

# a tree step as a crown step with no help leaf
def lifted(s: T.Step) -> A.CStep:
  match s:
    case T.Took{n}:
      A.CTook{A.Crown{n, []}}
    case T.Refused{why}:
      A.CRefused{why}

# T14: the event e is a tick whose now is past the deadline dl
def tick_up(dl: T.Lim, e: T.Ev) -> Bool:
  match e:
    case T.EvSplit{at, own, ls, rs, hold}:
      False{}
    case T.EvSpend{at, n}:
      False{}
    case T.EvFinish{at, q}:
      False{}
    case T.EvFail{at, q}:
      False{}
    case T.EvCancel{at}:
      False{}
    case T.EvRedo{at, side, extra}:
      False{}
    case T.EvTick{now}:
      S.up(dl, now)

def stopped(stop: Bool, st: T.Status) -> T.Status:
  match stop:
    case True{}:
      T.Cancelled{}
    case False{}:
      st

# T14: every running help leaf whose node does not run in t, or whose own
# deadline the tick e finds up, cancelled
def swept(+t: T.Node, +e: T.Ev, hs: List<&2, A.Help>) -> List<&2, A.Help>:
  match hs:
    case Nil{}:
      []
    case Con{h, rest}:
      match h:
        case A.Help{+p, +st, lim, sp, +dl}:
          A.Help{p, stopped(Bool.and(T.running(st), Bool.or(Bool.not(CS.runs_at(S.node_at(p, t))), tick_up(dl, e))), st), lim, sp, dl} <> swept(t, e, rest)

# T14: a tree event: the tree's step on the view with max_nodes less the
# help leaves; taken: the charges taken off again, the help leaves swept
def tree_spec_of(s: T.Step, +hs: List<&2, A.Help>, +e: T.Ev) -> A.CStep:
  match s:
    case T.Took{x}:
      +t2 = CS.unview_of(x, hs)
      A.CTook{A.Crown{t2, swept(t2, e, hs)}}
    case T.Refused{why}:
      A.CRefused{why}

def tree_spec(+b: T.Bounds, +c: A.Crown, +e: T.Ev) -> A.CStep:
  tree_spec_of(T.step(CS.bounds(b, c), CS.view(c), e), CS.helps_of(c), e)

# T14: a help leaf's limit: Unlimited under an Unlimited room, else a
def granted(room: T.Lim, a: Nat) -> T.Lim:
  match room:
    case T.Unlimited{}:
      T.Unlimited{}
    case T.Value{m}:
      T.Value{a}

# T14: a help of a at p, n the view's node there: the checks in order, and
# the help leaf appended (running, its limit granted from the room, nothing
# spent, the node's deadline less the margin)
def help_spec_at(m: Maybe<&2, T.Node>, +b: T.Bounds, +t: T.Node, +hs: List<&2, A.Help>, +p: List<&2, T.Dir>, +a: Nat) -> A.CStep:
  match m:
    case None{}:
      A.CRefused{T.NoNode{}}
    case Some{+n}:
      cdecided(AgentTree.first_failed([AgentTree.Check{S.is_running(n), T.NotRunning{}}, AgentTree.Check{Nat.is_le(Nat.add(Nat.add(S.nodes(t), CS.count(hs)), 1n), T.bound_nodes(b)), T.TooMany{}}, AgentTree.Check{S.has(a, S.room(n)), T.NoBudget{}}]), A.Crown{t, List.append(&2, A.Help, hs, [A.Help{p, T.Running{}, granted(S.room(n), a), 0n, S.minus(T.deadline_of(T.info(n)), T.bound_margin(b))}])})

def help_spec(+b: T.Bounds, c: A.Crown, +p: List<&2, T.Dir>, +a: Nat) -> A.CStep:
  match c:
    case A.Crown{+t, +hs}:
      help_spec_at(S.node_at(p, CS.view_of(t, hs)), b, t, hs, p, a)

# T14: help leaf k spends a: running, a within its limit less its spend
def spend_spec_at(m: Maybe<&2, A.Help>, +t: T.Node, +hs: List<&2, A.Help>, +k: Nat, +a: Nat) -> A.CStep:
  match m:
    case None{}:
      A.CRefused{T.NoNode{}}
    case Some{h}:
      match h:
        case A.Help{p, +st, +lim, +sp, dl}:
          cdecided(AgentTree.first_failed([AgentTree.Check{T.running(st), T.NotRunning{}}, AgentTree.Check{S.has(a, S.minus(lim, sp)), T.NoBudget{}}]), A.Crown{t, CS.set(hs, k, A.Help{p, st, lim, Nat.add(sp, a), dl})})

def help_spend_spec(c: A.Crown, +k: Nat, +a: Nat) -> A.CStep:
  match c:
    case A.Crown{+t, +hs}:
      spend_spec_at(CS.nth(hs, k), t, hs, k, a)

def settled(ok: Bool) -> T.Status:
  match ok:
    case True{}:
      T.Finished{}
    case False{}:
      T.Failed{}

# T14: help leaf k settles: running, then Finished (ok) or Failed
def end_spec_at(m: Maybe<&2, A.Help>, +t: T.Node, +hs: List<&2, A.Help>, +k: Nat, ok: Bool) -> A.CStep:
  match m:
    case None{}:
      A.CRefused{T.NoNode{}}
    case Some{h}:
      match h:
        case A.Help{p, st, lim, sp, dl}:
          cdecided(AgentTree.first_failed([AgentTree.Check{T.running(st), T.NotRunning{}}]), A.Crown{t, CS.set(hs, k, A.Help{p, settled(ok), lim, sp, dl})})

def help_end_spec(c: A.Crown, +k: Nat, ok: Bool) -> A.CStep:
  match c:
    case A.Crown{+t, +hs}:
      end_spec_at(CS.nth(hs, k), t, hs, k, ok)

# T14: the step a settled finish leaves: no help leaf at p runs
def help_quiet_at(+p: List<&2, T.Dir>, s: A.CStep) -> Bool:
  match s:
    case A.CTook{c}:
      CS.none_run_at(p, CS.helps_of(c))
    case A.CRefused{why}:
      True{}

# Laws: decisions (T14)
# ---------------------

# LAW crown_help_is_spec (T14): a help of a at the path p of any crown is
# refused NoNode when the view has no node at p, else with the first of
# NotRunning (the node does not run), TooMany (the tree's nodes plus the
# help leaves plus one past max_nodes), NoBudget (a past the room of the
# view's node: its limit less its spend, the charges of its help leaves
# and what its children hold) that fails; else a running help leaf at p
# is appended, nothing spent, its limit a (Unlimited when the room is),
# its deadline the node's less the margin; the tree is unchanged
# EXCLUDES: a help of a settled node; a help leaf not counted in
#   max_nodes; a help whose budget ignores the other help leaves' charges;
#   a help leaf given the node's whole room or a deadline past the node's;
#   a help that changes the tree
law crown_help_is_spec:
  for +b: T.Bounds
  for +c: A.Crown
  for +p: List<&2, T.Dir>
  for +a: Nat
  {A.hstep(b, c, A.EvHelp{p, a}) == help_spec(b, c, p, a) : A.CStep}

# LAW crown_help_spend_is_spec (T14): help leaf k spending a is refused
# NoNode when there is no help leaf k, NotRunning when it does not run,
# NoBudget when a is past its limit less its spend; else its spend grows
# by a and nothing else changes
# EXCLUDES: a settled help leaf spending; a spend past the help leaf's
#   limit; a spend charged to another help leaf or to the tree
law crown_help_spend_is_spec:
  for +b: T.Bounds
  for +c: A.Crown
  for +k: Nat
  for +a: Nat
  {A.hstep(b, c, A.EvHelpSpend{k, a}) == help_spend_spec(c, k, a) : A.CStep}

# LAW crown_help_end_is_spec (T14): help leaf k settling is refused NoNode
# when there is no help leaf k, NotRunning when it does not run; else it is
# Finished (ok) or Failed (not ok) with its spend kept, and nothing else
# changes
# EXCLUDES: a settled help leaf settled again; ok and not ok swapped; the
#   spend reset on settling
law crown_help_end_is_spec:
  for +b: T.Bounds
  for +c: A.Crown
  for +k: Nat
  for ok: Bool
  {A.hstep(b, c, A.EvHelpEnd{k, ok}) == help_end_spec(c, k, ok) : A.CStep}

# LAW crown_tree_is_spec (T14): a tree event e on any crown is the tree's
# step on the view (each node's spent raised by the charges of the help
# leaves at its path) under the bounds with max_nodes less the number of
# help leaves; refused: the same refusal; taken: the new tree with the same
# charges taken off again at the same paths, and every running help leaf
# whose node does not run in it, or (a tick at now) whose deadline is up at
# now, cancelled, nothing else of the help leaves changed
# EXCLUDES: tree decisions that ignore the help leaves' charges; charges
#   left in the stored tree; help leaves left running under a cancelled,
#   failed or finished node; a tick that skips the help leaves' deadlines;
#   help leaves not counted against max_nodes
law crown_tree_is_spec:
  for +b: T.Bounds
  for +c: A.Crown
  for +e: T.Ev
  {A.hstep(b, c, A.OnTree{e}) == tree_spec(b, c, e) : A.CStep}

# LAW crown_tree_alone (T14): with no help leaf a tree event is exactly the
# tree's step (refused with its reason, or taken with its tree and still
# no help leaf), so every tree law (T1-T11) carries over
# EXCLUDES: a crown that changes the bounds or the tree when no help leaf
#   exists; one that invents a help leaf
law crown_tree_alone:
  for +b: T.Bounds
  for +t: T.Node
  for +e: T.Ev
  {A.hstep(b, A.Crown{t, []}, A.OnTree{e}) == lifted(T.step(b, t, e)) : A.CStep}

# LAW crown_init_steps_as_tree (T14, T8): the crown a run starts from
# (scope s, limit lim, deadline dl) decides its first tree event exactly as
# the tree's own root init(s, lim, dl) does, so the root starts running
# with the configured scope, limit and deadline and no help leaf
# EXCLUDES: a crown root that starts settled (every spend refused); one
#   that drops the configured scope, limit or deadline
law crown_init_steps_as_tree:
  for +b: T.Bounds
  for s: List<&2, Bool>
  for lim: T.Lim
  for dl: T.Lim
  for +e: T.Ev
  {A.hstep(b, A.cinit(s, lim, dl), A.OnTree{e}) == lifted(T.step(b, T.init(s, lim, dl), e)) : A.CStep}

# LAW crown_init_root (T14, T8): the crown a run starts from is one running
# leaf over the configured scope s with the configured limit lim and
# deadline dl, nothing spent, no patch, and no help leaf
# EXCLUDES: a root that starts settled, with another scope, limit or
#   deadline, something spent or a patch; a crown that starts with a help
#   leaf
law crown_init_root:
  for s: List<&2, Bool>
  for lim: T.Lim
  for dl: T.Lim
  {A.cinit(s, lim, dl) == A.Crown{T.Leaf{T.Info{T.Running{}, s, lim, 0n, dl, []}}, []} : A.Crown}

# LAW crown_help_overlay_nothing (T14): a help leaf h has no write scope:
# integrating its patch a over any parent patch cur applies nothing, and
# every unit it wrote is reported as a conflict, and only those
# EXCLUDES: a help leaf given its node's scope; its writes applied; its
#   writes dropped without a conflict
law crown_help_overlay_nothing:
  for +h: A.Help
  for +cur: List<&2, Maybe<&2, Nat>>
  for +a: List<&2, Maybe<&2, Nat>>
  {T.overlay(cur, a, A.hscope(h)) == cur : List<&2, Maybe<&2, Nat>>} & {T.conflicts(a, A.hscope(h)) == S.writes(a) : List<&2, Bool>}

# T14: the room of the node a Maybe holds (no node: None)
def room_at(m: Maybe<&2, T.Node>) -> Maybe<&2, T.Lim>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      Some{S.room(n)}

# LAW crown_free_is_spec (T14): the free a crown reports at p (cfree, what
# Rust shows a node before it asks a help) is the room of the view's node
# at p, and None when the view has no node there
# EXCLUDES: a free read off the tree without the help leaves' charges; a
#   free of the parent or the root; a free reported for a missing node
law crown_free_is_spec:
  for +c: A.Crown
  for +p: List<&2, T.Dir>
  {A.cfree(c, p) == room_at(S.node_at(p, CS.view(c))) : Maybe<&2, T.Lim>}

# LAW crown_never_blocks (T14): a finish at p is taken exactly when the
# tree's step on the view takes it (a running help leaf never blocks its
# node's settle), and once taken no help leaf at p runs
# EXCLUDES: a finish refused while a help leaf at the node runs; help
#   leaves left running at a finished node
law crown_never_blocks:
  for +b: T.Bounds
  for +c: A.Crown
  for +p: List<&2, T.Dir>
  for +q: List<&2, Maybe<&2, Nat>>
  {ctook(A.hstep(b, c, A.OnTree{T.EvFinish{p, q}})) == took(T.step(CS.bounds(b, c), CS.view(c), T.EvFinish{p, q})) : Bool} & {help_quiet_at(p, A.hstep(b, c, A.OnTree{T.EvFinish{p, q}})) == True{} : Bool}

# Laws: run (T14: "reachable")
# ----------------------------

# LAW crown_run_none (T14): running no event leaves the crown as it is
# EXCLUDES: a run that resets the crown to a fresh root
law crown_run_none:
  for +b: T.Bounds
  for +c: A.Crown
  {A.crun([], b, c) == c : A.Crown}

# LAW crown_run_last (T14): running evs then one more event e is the step
# of e on the crown evs reached (the old crown kept when e is refused)
# EXCLUDES: a run that ignores its events; one that drops the last event;
#   one that applies a refused event's partial work
law crown_run_last:
  for evs: List<&2, A.CEv>
  for +e: A.CEv
  for +b: T.Bounds
  for +c: A.Crown
  {A.crun(List.append(&2, A.CEv, evs, [e]), b, c) == clanded(A.hstep(b, A.crun(evs, b, c), e), A.crun(evs, b, c)) : A.Crown}

# Laws: reachable crowns (T14)
# ----------------------------

# LAW crown_no_orphan (T14): in every reachable crown every running help
# leaf's node runs (a cancel, fail, finish or tick of the node or above it
# cancels its help leaves)
# EXCLUDES: help leaves left running under a cancelled or failed subtree;
#   a help admitted at a settled node; a tick that cancels a node but not
#   its help leaves
law crown_no_orphan:
  for evs: List<&2, A.CEv>
  for +b: T.Bounds
  for s: List<&2, Bool>
  for lim: T.Lim
  for dl: T.Lim
  {CS.helps_placed(A.crun(evs, b, A.cinit(s, lim, dl))) == True{} : Bool}

# LAW crown_budget_holds (T14): in every crown reachable from a root with
# the limit Value m, the tree's whole spend plus every help leaf's spend is
# at most m
# EXCLUDES: help leaves granted budget the tree also spends; a help spend
#   past its limit; a settled help leaf's spend dropped from its node's
#   free; tree decisions that ignore the help leaves
law crown_budget_holds:
  for evs: List<&2, A.CEv>
  for +b: T.Bounds
  for s: List<&2, Bool>
  for +m: Nat
  for dl: T.Lim
  {Nat.is_le(CS.crown_spent(A.crun(evs, b, A.cinit(s, T.Value{m}, dl))), m) == True{} : Bool}

# LAW crown_nodes_bound (T14): with max_nodes at least one, in every
# reachable crown the tree's nodes plus the help leaves are at most
# max_nodes
# EXCLUDES: help leaves not counted against max_nodes; a split that
#   ignores the help leaves; the help check off by one
law crown_nodes_bound:
  for evs: List<&2, A.CEv>
  for +b: T.Bounds
  for s: List<&2, Bool>
  for lim: T.Lim
  for dl: T.Lim
  for e: {Nat.is_le(1n, T.bound_nodes(b)) == True{} : Bool}
  {Nat.is_le(CS.crown_nodes(A.crun(evs, b, A.cinit(s, lim, dl))), T.bound_nodes(b)) == True{} : Bool}
