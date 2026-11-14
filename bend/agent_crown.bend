# agent_crown: the binary agent tree (bend/agent_tree.bend) crowned with
# help leaves. Writers form the tree; a running node may ask a read-only
# helper (help(task)): an extra leaf with no write scope, counted in
# max_nodes, its budget taken from the node's free, cancelled with the
# subtree, settling like a child.
#
# A help leaf charges the node at its path: while it runs its limit (an
# Unlimited one: nothing), once settled what it spent. Every tree decision
# is taken on the view: the tree with each node's spent raised by the
# charges of the help leaves at its path; the charges are taken off again
# after the decision.
#
# Pure: no IO, no @unsafe.

import Base
import ./agent_tree.bend as T

# Types
# -----

# a help leaf: the path of the node that asked it, its status, limit,
# spend and deadline
type Help is Data:
  Help{at: List<&2, T.Dir>, st: T.Status, limit: T.Lim, spent: Nat, deadline: T.Lim}

# the tree and every help leaf ever admitted, in order
type Crown is Data:
  Crown{t: T.Node, hs: List<&2, Help>}

type CEv is Data:
  OnTree{e: T.Ev}
  EvHelp{at: List<&2, T.Dir>, amount: Nat}
  EvHelpSpend{k: Nat, amount: Nat}
  EvHelpEnd{k: Nat, ok: Bool}

type CStep is Data:
  CTook{c: Crown}
  CRefused{why: T.Refusal}

# a help leaf has no write scope
def hscope(h: Help) -> List<&2, Bool>:
  match h:
    case Help{p, st, lim, sp, dl}:
      []

# Charges
# -------

def lim_n(l: T.Lim) -> Nat:
  match l:
    case T.Unlimited{}:
      0n
    case T.Value{n}:
      n

# a running help leaf charges its limit, a settled one what it spent
def charge_if(run: Bool, lim: T.Lim, sp: Nat) -> Nat:
  match run:
    case True{}:
      lim_n(lim)
    case False{}:
      sp

# what a help leaf charges, at its path
type Load is Data:
  Load{at: List<&2, T.Dir>, n: Nat}

def load_of(h: Help) -> Load:
  match h:
    case Help{p, st, lim, sp, dl}:
      Load{p, charge_if(T.running(st), lim, sp)}

def loads(hs: List<&2, Help>) -> List<&2, Load>:
  match hs:
    case Nil{}:
      []
    case Con{h, rest}:
      load_of(h) <> loads(rest)

# the charges at the path []
def here(ls: List<&2, Load>) -> Nat:
  match ls:
    case Nil{}:
      0n
    case Con{x, rest}:
      match x:
        case Load{p, n}:
          match p:
            case Nil{}:
              Nat.add(n, here(rest))
            case Con{e, q}:
              here(rest)

# the charges below the child d, their paths from that child
def down(ls: List<&2, Load>, +d: T.Dir) -> List<&2, Load>:
  match ls:
    case Nil{}:
      []
    case Con{x, rest}:
      match x:
        case Load{p, n}:
          match p:
            case Nil{}:
              down(rest, d)
            case Con{e, q}:
              match e:
                case T.GoL{}:
                  match d:
                    case T.GoL{}:
                      Load{q, n} <> down(rest, T.GoL{})
                    case T.GoR{}:
                      down(rest, T.GoR{})
                case T.GoR{}:
                  match d:
                    case T.GoL{}:
                      down(rest, T.GoL{})
                    case T.GoR{}:
                      Load{q, n} <> down(rest, T.GoR{})

# The view
# --------

# sp raised by n (up) or lowered by n (floor 0)
def bump_by(up: Bool, sp: Nat, n: Nat) -> Nat:
  match up:
    case True{}:
      Nat.add(sp, n)
    case False{}:
      Nat.sub(sp, n)

def shift_info(i: T.Info, up: Bool, n: Nat) -> T.Info:
  match i:
    case T.Info{st, s, lim, sp, dl, p}:
      T.Info{st, s, lim, bump_by(up, sp, n), dl, p}

# every node's spent raised (up) or lowered by the charges at its path
def shift(t: T.Node, +ls: List<&2, Load>, +up: Bool) -> T.Node:
  match t:
    case T.Leaf{i}:
      T.Leaf{shift_info(i, up, here(ls))}
    case T.Split{i, own, l, r}:
      T.Split{shift_info(i, up, here(ls)), own, shift(l, down(ls, T.GoL{}), up), shift(r, down(ls, T.GoR{}), up)}

# the tree every decision is taken on
def view(t: T.Node, hs: List<&2, Help>) -> T.Node:
  shift(t, loads(hs), True{})

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

def free_of(m: Maybe<&2, T.Node>) -> Maybe<&2, T.Lim>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      Some{T.free(n)}

# the free of the view's node at p (no node: None)
def cfree(c: Crown, p: List<&2, T.Dir>) -> Maybe<&2, T.Lim>:
  match c:
    case Crown{t, hs}:
      free_of(node_at(p, view(t, hs)))

def hcount(hs: List<&2, Help>) -> Nat:
  match hs:
    case Nil{}:
      0n
    case Con{h, rest}:
      1n+hcount(rest)

# the tree's bounds with the help leaves' nodes taken from max_nodes
def cbounds(b: T.Bounds, hs: List<&2, Help>) -> T.Bounds:
  match b:
    case T.Bounds{d, n, m}:
      T.Bounds{d, Nat.sub(n, hcount(hs)), m}

# Tree events
# -----------

def runs(m: Maybe<&2, T.Node>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{n}:
      T.running(T.st_of(T.info(n)))

# the help leaf's own deadline is up (only a tick checks deadlines)
def help_late(dl: T.Lim, e: T.Ev) -> Bool:
  match e:
    case T.EvSplit{at, own, ls, rs, hold}:
      False{}
    case T.EvSpend{at, n}:
      False{}
    case T.EvFinish{at, p}:
      False{}
    case T.EvFail{at, p}:
      False{}
    case T.EvCancel{at}:
      False{}
    case T.EvRedo{at, side, extra}:
      False{}
    case T.EvTick{now}:
      T.lim_up(dl, now)

def sweep_st(stop: Bool, st: T.Status) -> T.Status:
  match stop:
    case True{}:
      T.cancel_st(st)
    case False{}:
      st

# every running help leaf whose node does not run in t, or whose own
# deadline the event e finds up, cancelled
def sweep(hs: List<&2, Help>, +t: T.Node, +e: T.Ev) -> List<&2, Help>:
  match hs:
    case Nil{}:
      []
    case Con{h, rest}:
      match h:
        case Help{+p, st, lim, sp, +dl}:
          Help{p, sweep_st(Bool.or(Bool.not(runs(node_at(p, t))), help_late(dl, e)), st), lim, sp, dl} <> sweep(rest, t, e)

# the tree's decision s on the view: the charges taken off again, the help
# leaves swept
def on_tree(s: T.Step, +hs: List<&2, Help>, e: T.Ev) -> CStep:
  match s:
    case T.Took{x}:
      +t2 = shift(x, loads(hs), False{})
      CTook{Crown{t2, sweep(hs, t2, e)}}
    case T.Refused{why}:
      CRefused{why}

# Help events
# -----------

# a help leaf's limit: Unlimited under a node with Unlimited free, else a
def grant(f: T.Lim, a: Nat) -> T.Lim:
  match f:
    case T.Unlimited{}:
      T.Unlimited{}
    case T.Value{m}:
      T.Value{a}

def help_fit(ok: Bool, +n: T.Node, t: T.Node, hs: List<&2, Help>, p: List<&2, T.Dir>, a: Nat, margin: Nat) -> CStep:
  match ok:
    case True{}:
      CTook{Crown{t, List.append(&2, Help, hs, [Help{p, T.Running{}, grant(T.free(n), a), 0n, T.lim_less(T.deadline_of(T.info(n)), margin)}])}}
    case False{}:
      CRefused{T.NoBudget{}}

def help_room(room: Bool, +n: T.Node, t: T.Node, hs: List<&2, Help>, p: List<&2, T.Dir>, +a: Nat, margin: Nat) -> CStep:
  match room:
    case True{}:
      help_fit(T.lim_fits(a, T.free(n)), n, t, hs, p, a, margin)
    case False{}:
      CRefused{T.TooMany{}}

def help_run(run: Bool, n: T.Node, t: T.Node, hs: List<&2, Help>, p: List<&2, T.Dir>, a: Nat, room: Bool, margin: Nat) -> CStep:
  match run:
    case True{}:
      help_room(room, n, t, hs, p, a, margin)
    case False{}:
      CRefused{T.NotRunning{}}

def help_node(m: Maybe<&2, T.Node>, t: T.Node, hs: List<&2, Help>, p: List<&2, T.Dir>, a: Nat, room: Bool, margin: Nat) -> CStep:
  match m:
    case None{}:
      CRefused{T.NoNode{}}
    case Some{+n}:
      help_run(T.running(T.st_of(T.info(n))), n, t, hs, p, a, room, margin)

# a change to the help leaves: the new list, or the refusal
type HRes is Data:
  HOk{hs: List<&2, Help>}
  HNo{why: T.Refusal}

def hres_cons(h: Help, r: HRes) -> HRes:
  match r:
    case HOk{xs}:
      HOk{h <> xs}
    case HNo{why}:
      HNo{why}

def hrunning(h: Help) -> Bool:
  match h:
    case Help{p, st, lim, sp, dl}:
      T.running(st)

def spend_fit(ok: Bool, h: Help, a: Nat, rest: List<&2, Help>) -> HRes:
  match ok:
    case True{}:
      match h:
        case Help{p, st, lim, sp, dl}:
          HOk{Help{p, st, lim, Nat.add(sp, a), dl} <> rest}
    case False{}:
      HNo{T.NoBudget{}}

def spend_one(run: Bool, h: Help, +a: Nat, rest: List<&2, Help>) -> HRes:
  match run:
    case True{}:
      match h:
        case Help{p, st, +lim, +sp, dl}:
          spend_fit(T.lim_fits(a, T.lim_less(lim, sp)), Help{p, st, lim, sp, dl}, a, rest)
    case False{}:
      HNo{T.NotRunning{}}

# help leaf k spends a
def spend_k(k: Nat, hs: List<&2, Help>, a: Nat) -> HRes:
  match k:
    case 0n:
      match hs:
        case Nil{}:
          HNo{T.NoNode{}}
        case Con{+h, rest}:
          spend_one(hrunning(h), h, a, rest)
    case 1n+j:
      match hs:
        case Nil{}:
          HNo{T.NoNode{}}
        case Con{h, rest}:
          hres_cons(h, spend_k(j, rest, a))

def end_st(ok: Bool) -> T.Status:
  match ok:
    case True{}:
      T.Finished{}
    case False{}:
      T.Failed{}

def end_one(run: Bool, h: Help, ok: Bool, rest: List<&2, Help>) -> HRes:
  match run:
    case True{}:
      match h:
        case Help{p, st, lim, sp, dl}:
          HOk{Help{p, end_st(ok), lim, sp, dl} <> rest}
    case False{}:
      HNo{T.NotRunning{}}

# help leaf k settles: Finished (ok) or Failed
def end_k(k: Nat, hs: List<&2, Help>, ok: Bool) -> HRes:
  match k:
    case 0n:
      match hs:
        case Nil{}:
          HNo{T.NoNode{}}
        case Con{+h, rest}:
          end_one(hrunning(h), h, ok, rest)
    case 1n+j:
      match hs:
        case Nil{}:
          HNo{T.NoNode{}}
        case Con{h, rest}:
          hres_cons(h, end_k(j, rest, ok))

def hres_crown(r: HRes, t: T.Node) -> CStep:
  match r:
    case HOk{xs}:
      CTook{Crown{t, xs}}
    case HNo{why}:
      CRefused{why}

# The step
# --------

# the decision on an event: the new crown, or the refusal (the crown stays)
def hstep(+b: T.Bounds, c: Crown, e: CEv) -> CStep:
  match c:
    case Crown{+t, +hs}:
      match e:
        case OnTree{+ev}:
          on_tree(T.step(cbounds(b, hs), view(t, hs), ev), hs, ev)
        case EvHelp{+p, a}:
          help_node(node_at(p, view(t, hs)), t, hs, p, a, Nat.is_le(Nat.add(Nat.add(T.size(t), hcount(hs)), 1n), T.bound_nodes(b)), T.bound_margin(b))
        case EvHelpSpend{k, a}:
          hres_crown(spend_k(k, hs, a), t)
        case EvHelpEnd{k, ok}:
          hres_crown(end_k(k, hs, ok), t)

def cafter(s: CStep, c: Crown) -> Crown:
  match s:
    case CTook{n}:
      n
    case CRefused{why}:
      c

# the crown after the events evs, in order, from c
def crun(evs: List<&2, CEv>, +b: T.Bounds, +c: Crown) -> Crown:
  match evs:
    case Nil{}:
      c
    case Con{e, es}:
      crun(es, b, cafter(hstep(b, c, e), c))

# the root crown: the tree's root, no help leaf
def cinit(s: List<&2, Bool>, lim: T.Lim, dl: T.Lim) -> Crown:
  Crown{T.init(s, lim, dl), []}
