# agent_tree: the decisions of a binary agent tree. A node works alone (a
# leaf) or splits into exactly two children; each node owns a scope (a
# mask over the repository's units: true = owned); the parent integrates
# its children's patches and reports up.
#
# Units are positions: a scope is a list of Bool, a patch a list of
# Maybe<Nat> (Some = the unit's new bytes, None = untouched), the files a
# list of Nat (the bytes of each unit). A list shorter than another reads
# False / None past its end.
#
# Budget and deadline are Lim: Unlimited (the default run: until finished)
# or a Value. A settled child charges its parent what its subtree spent;
# a running child its whole limit, so a child's unspent limit returns to
# its parent's free when it settles.
#
# Pure: no IO, no @unsafe.

import Base

# Numbers
# -------

# an amount or a deadline: none, or a value
type Lim is Data:
  Unlimited{}
  Value{n: Nat}

def pred(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      p

# n halved, rounded down
def half(n: Nat) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      match p:
        case 0n:
          0n
        case 1n+q:
          1n+half(q)

# n fits within l
def lim_fits(n: Nat, l: Lim) -> Bool:
  match l:
    case Unlimited{}:
      True{}
    case Value{m}:
      Nat.is_le(n, m)

# l less n (floor 0)
def lim_less(l: Lim, n: Nat) -> Lim:
  match l:
    case Unlimited{}:
      Unlimited{}
    case Value{m}:
      Value{Nat.sub(m, n)}

# a less b (floor 0; Unlimited less a value stays Unlimited)
def lim_drop(a: Lim, b: Lim) -> Lim:
  match a b:
    case Unlimited{} Unlimited{}:
      Unlimited{}
    case Unlimited{} Value{y}:
      Unlimited{}
    case Value{x} Unlimited{}:
      Value{0n}
    case Value{x} Value{y}:
      Value{Nat.sub(x, y)}

# the larger half of l
def half_hi(l: Lim) -> Lim:
  match l:
    case Unlimited{}:
      Unlimited{}
    case Value{+c}:
      Value{Nat.sub(c, half(c))}

# the smaller half of l
def half_lo(l: Lim) -> Lim:
  match l:
    case Unlimited{}:
      Unlimited{}
    case Value{c}:
      Value{half(c)}

# Nodes
# -----

type Status is Data:
  Running{}
  Finished{}
  Failed{}
  Cancelled{}

type Dir is Data:
  GoL{}
  GoR{}

# status, scope, limit, spent, deadline, and the node's patch (a leaf: its
# work; a split: its own work and integration, applied after its children)
type Info is Data:
  Info{st: Status, scope: List<&2, Bool>, limit: Lim, spent: Nat, deadline: Lim, patch: List<&2, Maybe<&2, Nat>>}

type Node is Data:
  Leaf{i: Info}
  Split{i: Info, own: List<&2, Bool>, l: Node, r: Node}

# the configured bounds: depth, node count, and the integration margin a
# child's deadline keeps before its parent's
type Bounds is Data:
  Bounds{max_depth: Nat, max_nodes: Nat, margin: Nat}

def info(t: Node) -> Info:
  match t:
    case Leaf{i}:
      i
    case Split{i, own, l, r}:
      i

def st_of(i: Info) -> Status:
  match i:
    case Info{st, s, lim, sp, dl, p}:
      st

def scope_of(i: Info) -> List<&2, Bool>:
  match i:
    case Info{st, s, lim, sp, dl, p}:
      s

def limit_of(i: Info) -> Lim:
  match i:
    case Info{st, s, lim, sp, dl, p}:
      lim

def spent_of(i: Info) -> Nat:
  match i:
    case Info{st, s, lim, sp, dl, p}:
      sp

def deadline_of(i: Info) -> Lim:
  match i:
    case Info{st, s, lim, sp, dl, p}:
      dl

def patch_of(i: Info) -> List<&2, Maybe<&2, Nat>>:
  match i:
    case Info{st, s, lim, sp, dl, p}:
      p

def running(st: Status) -> Bool:
  match st:
    case Running{}:
      True{}
    case Finished{}:
      False{}
    case Failed{}:
      False{}
    case Cancelled{}:
      False{}

# the node count
def size(t: Node) -> Nat:
  match t:
    case Leaf{i}:
      1n
    case Split{i, own, l, r}:
      1n+Nat.add(size(l), size(r))

# what the subtree spent
def total(t: Node) -> Nat:
  match t:
    case Leaf{i}:
      spent_of(i)
    case Split{i, own, l, r}:
      Nat.add(spent_of(i), Nat.add(total(l), total(r)))

# what a child holds of its parent: its limit while it runs, what its
# subtree spent once settled
def charge_st(st: Status, lim: Lim, sp: Nat) -> Lim:
  match st:
    case Running{}:
      lim
    case Finished{}:
      Value{sp}
    case Failed{}:
      Value{sp}
    case Cancelled{}:
      Value{sp}

def charge(+t: Node) -> Lim:
  charge_st(st_of(info(t)), limit_of(info(t)), total(t))

# what a node may still spend or give
def free(t: Node) -> Lim:
  match t:
    case Leaf{+i}:
      lim_less(limit_of(i), spent_of(i))
    case Split{+i, own, +l, +r}:
      lim_drop(lim_drop(lim_less(limit_of(i), spent_of(i)), charge(l)), charge(r))

def cancel_st(st: Status) -> Status:
  match st:
    case Running{}:
      Cancelled{}
    case Finished{}:
      Finished{}
    case Failed{}:
      Failed{}
    case Cancelled{}:
      Cancelled{}

def cancel_info(i: Info) -> Info:
  match i:
    case Info{st, s, lim, sp, dl, p}:
      Info{cancel_st(st), s, lim, sp, dl, p}

# every running node of t cancelled
def cancel_all(t: Node) -> Node:
  match t:
    case Leaf{i}:
      Leaf{cancel_info(i)}
    case Split{i, own, l, r}:
      Split{cancel_info(i), own, cancel_all(l), cancel_all(r)}

# the root: a running leaf over the whole scope, nothing spent
def init(s: List<&2, Bool>, lim: Lim, dl: Lim) -> Node:
  Leaf{Info{Running{}, s, lim, 0n, dl, []}}

# Events
# ------

type Ev is Data:
  EvSplit{at: List<&2, Dir>, own: List<&2, Bool>, ls: List<&2, Bool>, rs: List<&2, Bool>, hold: Nat}
  EvSpend{at: List<&2, Dir>, amount: Nat}
  EvFinish{at: List<&2, Dir>, patch: List<&2, Maybe<&2, Nat>>}
  EvFail{at: List<&2, Dir>, patch: List<&2, Maybe<&2, Nat>>}
  EvCancel{at: List<&2, Dir>}
  EvRedo{at: List<&2, Dir>, side: Dir, extra: Nat}
  EvTick{now: Nat}

type Refusal is Data:
  NoNode{}
  NotRunning{}
  NotLeaf{}
  TooDeep{}
  TooMany{}
  BadScopes{}
  NoBudget{}
  Unsettled{}
  NotRedoable{}

type Step is Data:
  Took{t: Node}
  Refused{why: Refusal}

# what an event does at the node it names (room: the tree has room for
# two more nodes; margin: Bounds.margin)
type Op is Data:
  OpSplit{own: List<&2, Bool>, ls: List<&2, Bool>, rs: List<&2, Bool>, hold: Nat, room: Bool, margin: Nat}
  OpSpend{amount: Nat}
  OpFinish{patch: List<&2, Maybe<&2, Nat>>}
  OpFail{patch: List<&2, Maybe<&2, Nat>>}
  OpCancel{}
  OpRedo{side: Dir, extra: Nat}

# Split
# -----

# one unit of a split: outside the scope nobody owns it; inside exactly
# one of own, left, right does
def cell(s: Bool, o: Bool, +l: Bool, +r: Bool) -> Bool:
  match s:
    case True{}:
      match o:
        case True{}:
          Bool.not(Bool.or(l, r))
        case False{}:
          Bool.and(Bool.or(l, r), Bool.not(Bool.and(l, r)))
    case False{}:
      Bool.not(Bool.or(o, Bool.or(l, r)))

# own, ls and rs split the scope s unit by unit (all four of one length)
def tiles(s: List<&2, Bool>, o: List<&2, Bool>, l: List<&2, Bool>, r: List<&2, Bool>) -> Bool:
  match s o l r:
    case Nil{} Nil{} Nil{} Nil{}:
      True{}
    case Nil{} Nil{} Nil{} Con{c, ct}:
      False{}
    case Nil{} Nil{} Con{b, bt} Nil{}:
      False{}
    case Nil{} Nil{} Con{b, bt} Con{c, ct}:
      False{}
    case Nil{} Con{a, at} Nil{} Nil{}:
      False{}
    case Nil{} Con{a, at} Nil{} Con{c, ct}:
      False{}
    case Nil{} Con{a, at} Con{b, bt} Nil{}:
      False{}
    case Nil{} Con{a, at} Con{b, bt} Con{c, ct}:
      False{}
    case Con{x, xt} Nil{} Nil{} Nil{}:
      False{}
    case Con{x, xt} Nil{} Nil{} Con{c, ct}:
      False{}
    case Con{x, xt} Nil{} Con{b, bt} Nil{}:
      False{}
    case Con{x, xt} Nil{} Con{b, bt} Con{c, ct}:
      False{}
    case Con{x, xt} Con{a, at} Nil{} Nil{}:
      False{}
    case Con{x, xt} Con{a, at} Nil{} Con{c, ct}:
      False{}
    case Con{x, xt} Con{a, at} Con{b, bt} Nil{}:
      False{}
    case Con{x, xt} Con{a, at} Con{b, bt} Con{c, ct}:
      Bool.and(cell(x, a, b, c), tiles(xt, at, bt, ct))

# some unit is owned
def any(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case Con{x, t}:
      Bool.or(x, any(t))

# a new running child
def child(s: List<&2, Bool>, lim: Lim, dl: Lim) -> Node:
  Leaf{Info{Running{}, s, lim, 0n, dl, []}}

def split_budget(ok: Bool, +i: Info, own: List<&2, Bool>, ls: List<&2, Bool>, rs: List<&2, Bool>, +hold: Nat, +margin: Nat) -> Step:
  match ok:
    case True{}:
      +c = lim_less(lim_less(limit_of(i), spent_of(i)), hold)
      +d = lim_less(deadline_of(i), margin)
      Took{Split{i, own, child(ls, half_hi(c), d), child(rs, half_lo(c), d)}}
    case False{}:
      Refused{NoBudget{}}

def split_scopes(ok: Bool, +i: Info, own: List<&2, Bool>, ls: List<&2, Bool>, rs: List<&2, Bool>, +hold: Nat, margin: Nat) -> Step:
  match ok:
    case True{}:
      split_budget(lim_fits(Nat.add(hold, 2n), lim_less(limit_of(i), spent_of(i))), i, own, ls, rs, hold, margin)
    case False{}:
      Refused{BadScopes{}}

def split_room(room: Bool, +i: Info, +own: List<&2, Bool>, +ls: List<&2, Bool>, +rs: List<&2, Bool>, hold: Nat, margin: Nat) -> Step:
  match room:
    case True{}:
      split_scopes(Bool.and(tiles(scope_of(i), own, ls, rs), Bool.and(any(ls), any(rs))), i, own, ls, rs, hold, margin)
    case False{}:
      Refused{TooMany{}}

def split_depth(k: Nat, i: Info, own: List<&2, Bool>, ls: List<&2, Bool>, rs: List<&2, Bool>, hold: Nat, room: Bool, margin: Nat) -> Step:
  match k:
    case 0n:
      Refused{TooDeep{}}
    case 1n+p:
      split_room(room, i, own, ls, rs, hold, margin)

def split_shape(t: Node, own: List<&2, Bool>, ls: List<&2, Bool>, rs: List<&2, Bool>, hold: Nat, room: Bool, margin: Nat, k: Nat) -> Step:
  match t:
    case Leaf{i}:
      split_depth(k, i, own, ls, rs, hold, room, margin)
    case Split{i, o, l, r}:
      Refused{NotLeaf{}}

def split_st(st: Status, t: Node, own: List<&2, Bool>, ls: List<&2, Bool>, rs: List<&2, Bool>, hold: Nat, room: Bool, margin: Nat, k: Nat) -> Step:
  match st:
    case Running{}:
      split_shape(t, own, ls, rs, hold, room, margin, k)
    case Finished{}:
      Refused{NotRunning{}}
    case Failed{}:
      Refused{NotRunning{}}
    case Cancelled{}:
      Refused{NotRunning{}}

# Spend
# -----

def add_spent_info(i: Info, n: Nat) -> Info:
  match i:
    case Info{st, s, lim, sp, dl, p}:
      Info{st, s, lim, Nat.add(sp, n), dl, p}

def add_spent(t: Node, n: Nat) -> Node:
  match t:
    case Leaf{i}:
      Leaf{add_spent_info(i, n)}
    case Split{i, own, l, r}:
      Split{add_spent_info(i, n), own, l, r}

def spend_fits(ok: Bool, t: Node, n: Nat) -> Step:
  match ok:
    case True{}:
      Took{add_spent(t, n)}
    case False{}:
      Refused{NoBudget{}}

def spend_st(st: Status, +t: Node, +n: Nat) -> Step:
  match st:
    case Running{}:
      spend_fits(lim_fits(n, free(t)), t, n)
    case Finished{}:
      Refused{NotRunning{}}
    case Failed{}:
      Refused{NotRunning{}}
    case Cancelled{}:
      Refused{NotRunning{}}

# Finish, fail
# ------------

def settle_info(i: Info, st: Status, p: List<&2, Maybe<&2, Nat>>) -> Info:
  match i:
    case Info{old, s, lim, sp, dl, q}:
      Info{st, s, lim, sp, dl, p}

def finish_settled(ok: Bool, i: Info, own: List<&2, Bool>, l: Node, r: Node, p: List<&2, Maybe<&2, Nat>>) -> Step:
  match ok:
    case True{}:
      Took{Split{settle_info(i, Finished{}, p), own, l, r}}
    case False{}:
      Refused{Unsettled{}}

def finish_shape(t: Node, p: List<&2, Maybe<&2, Nat>>) -> Step:
  match t:
    case Leaf{i}:
      Took{Leaf{settle_info(i, Finished{}, p)}}
    case Split{i, own, +l, +r}:
      finish_settled(Bool.and(Bool.not(running(st_of(info(l)))), Bool.not(running(st_of(info(r))))), i, own, l, r, p)

def finish_st(st: Status, t: Node, p: List<&2, Maybe<&2, Nat>>) -> Step:
  match st:
    case Running{}:
      finish_shape(t, p)
    case Finished{}:
      Refused{NotRunning{}}
    case Failed{}:
      Refused{NotRunning{}}
    case Cancelled{}:
      Refused{NotRunning{}}

# a failed node keeps its partial patch; its descendants are cancelled
def fail_node(t: Node, p: List<&2, Maybe<&2, Nat>>) -> Node:
  match t:
    case Leaf{i}:
      Leaf{settle_info(i, Failed{}, p)}
    case Split{i, own, l, r}:
      Split{settle_info(i, Failed{}, p), own, cancel_all(l), cancel_all(r)}

def fail_st(st: Status, t: Node, p: List<&2, Maybe<&2, Nat>>) -> Step:
  match st:
    case Running{}:
      Took{fail_node(t, p)}
    case Finished{}:
      Refused{NotRunning{}}
    case Failed{}:
      Refused{NotRunning{}}
    case Cancelled{}:
      Refused{NotRunning{}}

# Redo
# ----

# the new limit of a redone child: Unlimited under a parent with Unlimited
# free; else what it spent plus the extra
def regrant(f: Lim, sp: Nat, extra: Nat) -> Lim:
  match f:
    case Unlimited{}:
      Unlimited{}
    case Value{m}:
      Value{Nat.add(sp, extra)}

def redo_info(i: Info, lim: Lim) -> Info:
  match i:
    case Info{st, s, old, sp, dl, p}:
      Info{Running{}, s, lim, sp, dl, p}

def failed_or_cancelled(st: Status) -> Bool:
  match st:
    case Running{}:
      False{}
    case Finished{}:
      False{}
    case Failed{}:
      True{}
    case Cancelled{}:
      True{}

# the child c may be redone: a failed or cancelled leaf
def redoable(c: Node) -> Bool:
  match c:
    case Leaf{i}:
      failed_or_cancelled(st_of(i))
    case Split{i, own, l, r}:
      False{}

# the redone child
def redone(f: Lim, extra: Nat, c: Node) -> Node:
  match c:
    case Leaf{+i}:
      Leaf{redo_info(i, regrant(f, spent_of(i), extra))}
    case Split{i, own, l, r}:
      Split{i, own, l, r}

def redo_budget(ok: Bool, +f: Lim, i: Info, own: List<&2, Bool>, side: Dir, extra: Nat, l: Node, r: Node) -> Step:
  match ok:
    case True{}:
      match side:
        case GoL{}:
          Took{Split{i, own, redone(f, extra, l), r}}
        case GoR{}:
          Took{Split{i, own, l, redone(f, extra, r)}}
    case False{}:
      Refused{NoBudget{}}

def redo_child(ok: Bool, +f: Lim, i: Info, own: List<&2, Bool>, side: Dir, +extra: Nat, l: Node, r: Node) -> Step:
  match ok:
    case True{}:
      redo_budget(lim_fits(extra, f), f, i, own, side, extra, l, r)
    case False{}:
      Refused{NotRedoable{}}

def side_child(side: Dir, +l: Node, +r: Node) -> Node:
  match side:
    case GoL{}:
      l
    case GoR{}:
      r

def redo_split(t: Node, f: Lim, +side: Dir, extra: Nat) -> Step:
  match t:
    case Leaf{i}:
      Refused{NotRedoable{}}
    case Split{i, own, +l, +r}:
      redo_child(redoable(side_child(side, l, r)), f, i, own, side, extra, l, r)

def redo_shape(+t: Node, +side: Dir, extra: Nat) -> Step:
  redo_split(t, free(t), side, extra)

def redo_st(st: Status, t: Node, side: Dir, extra: Nat) -> Step:
  match st:
    case Running{}:
      redo_shape(t, side, extra)
    case Finished{}:
      Refused{NotRunning{}}
    case Failed{}:
      Refused{NotRunning{}}
    case Cancelled{}:
      Refused{NotRunning{}}

# The node at a path
# ------------------

# what op does at the node t, k levels of depth left below the limit
def local(op: Op, +t: Node, k: Nat) -> Step:
  match op:
    case OpSplit{own, ls, rs, hold, room, margin}:
      split_st(st_of(info(t)), t, own, ls, rs, hold, room, margin, k)
    case OpSpend{n}:
      spend_st(st_of(info(t)), t, n)
    case OpFinish{p}:
      finish_st(st_of(info(t)), t, p)
    case OpFail{p}:
      fail_st(st_of(info(t)), t, p)
    case OpCancel{}:
      Took{cancel_all(t)}
    case OpRedo{side, extra}:
      redo_st(st_of(info(t)), t, side, extra)

def wrap_l(i: Info, own: List<&2, Bool>, s: Step, r: Node) -> Step:
  match s:
    case Took{n}:
      Took{Split{i, own, n, r}}
    case Refused{why}:
      Refused{why}

def wrap_r(i: Info, own: List<&2, Bool>, l: Node, s: Step) -> Step:
  match s:
    case Took{n}:
      Took{Split{i, own, l, n}}
    case Refused{why}:
      Refused{why}

# op at the node the path p names, k levels of depth left
def edit(p: List<&2, Dir>, t: Node, op: Op, k: Nat) -> Step:
  match p:
    case Nil{}:
      local(op, t, k)
    case Con{d, rest}:
      match d:
        case GoL{}:
          match t:
            case Leaf{i}:
              Refused{NoNode{}}
            case Split{i, own, l, r}:
              wrap_l(i, own, edit(rest, l, op, pred(k)), r)
        case GoR{}:
          match t:
            case Leaf{i}:
              Refused{NoNode{}}
            case Split{i, own, l, r}:
              wrap_r(i, own, l, edit(rest, r, op, pred(k)))

def lim_up(dl: Lim, now: Nat) -> Bool:
  match dl:
    case Unlimited{}:
      False{}
    case Value{d}:
      Nat.is_le(d, now)

# a running node whose deadline is up at now
def expired(i: Info, now: Nat) -> Bool:
  match i:
    case Info{st, s, lim, sp, dl, p}:
      Bool.and(running(st), lim_up(dl, now))

def tick_info(up: Bool, i: Info) -> Info:
  match up:
    case True{}:
      cancel_info(i)
    case False{}:
      i

# every running node whose deadline is up at now is cancelled with its
# subtree (cut: an ancestor's deadline was up)
def tick(t: Node, +now: Nat, cut: Bool) -> Node:
  match t:
    case Leaf{+i}:
      Leaf{tick_info(Bool.or(cut, expired(i, now)), i)}
    case Split{+i, own, l, r}:
      +up = Bool.or(cut, expired(i, now))
      Split{tick_info(up, i), own, tick(l, now, up), tick(r, now, up)}

# The step
# --------

def bound_depth(b: Bounds) -> Nat:
  match b:
    case Bounds{d, n, m}:
      d

def bound_nodes(b: Bounds) -> Nat:
  match b:
    case Bounds{d, n, m}:
      n

def bound_margin(b: Bounds) -> Nat:
  match b:
    case Bounds{d, n, m}:
      m

# the decision on an event: the new tree, or the refusal (the tree stays)
def step(+b: Bounds, +t: Node, ev: Ev) -> Step:
  match ev:
    case EvSplit{at, own, ls, rs, hold}:
      edit(at, t, OpSplit{own, ls, rs, hold, Nat.is_le(Nat.add(size(t), 2n), bound_nodes(b)), bound_margin(b)}, bound_depth(b))
    case EvSpend{at, n}:
      edit(at, t, OpSpend{n}, bound_depth(b))
    case EvFinish{at, p}:
      edit(at, t, OpFinish{p}, bound_depth(b))
    case EvFail{at, p}:
      edit(at, t, OpFail{p}, bound_depth(b))
    case EvCancel{at}:
      edit(at, t, OpCancel{}, bound_depth(b))
    case EvRedo{at, side, extra}:
      edit(at, t, OpRedo{side, extra}, bound_depth(b))
    case EvTick{now}:
      Took{tick(t, now, False{})}

def after(s: Step, t: Node) -> Node:
  match s:
    case Took{n}:
      n
    case Refused{why}:
      t

# the tree after the events evs, in order, from t
def run(evs: List<&2, Ev>, +b: Bounds, +t: Node) -> Node:
  match evs:
    case Nil{}:
      t
    case Con{e, es}:
      run(es, b, after(step(b, t, e), t))

# Integration
# -----------

# one unit: the child's write when the unit is in its scope, else cur's
def pick(s: Bool, a: Maybe<&2, Nat>, c: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match s:
    case True{}:
      match a:
        case None{}:
          c
        case Some{x}:
          Some{x}
    case False{}:
      c

# the parent's patch cur with the child's patch a integrated: the child's
# writes inside its scope s replace cur's; its writes outside are dropped
# (reported by conflicts)
def overlay(cur: List<&2, Maybe<&2, Nat>>, a: List<&2, Maybe<&2, Nat>>, s: List<&2, Bool>) -> List<&2, Maybe<&2, Nat>>:
  match cur a s:
    case Nil{} Nil{} Nil{}:
      []
    case Nil{} Nil{} Con{b, bt}:
      []
    case Nil{} Con{x, xt} Nil{}:
      []
    case Nil{} Con{x, xt} Con{b, bt}:
      pick(b, x, None{}) <> overlay([], xt, bt)
    case Con{c, ct} Nil{} Nil{}:
      c <> ct
    case Con{c, ct} Nil{} Con{b, bt}:
      c <> ct
    case Con{c, ct} Con{x, xt} Nil{}:
      c <> ct
    case Con{c, ct} Con{x, xt} Con{b, bt}:
      pick(b, x, c) <> overlay(ct, xt, bt)

def written(a: Maybe<&2, Nat>) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{x}:
      True{}

# the units the child wrote outside its scope
def conflicts(a: List<&2, Maybe<&2, Nat>>, s: List<&2, Bool>) -> List<&2, Bool>:
  match a s:
    case Nil{} Nil{}:
      []
    case Nil{} Con{b, bt}:
      []
    case Con{x, xt} Nil{}:
      written(x) <> conflicts(xt, [])
    case Con{x, xt} Con{b, bt}:
      Bool.and(written(x), Bool.not(b)) <> conflicts(xt, bt)

# q's writes over p
def seq(p: List<&2, Maybe<&2, Nat>>, q: List<&2, Maybe<&2, Nat>>) -> List<&2, Maybe<&2, Nat>>:
  match p q:
    case Nil{} Nil{}:
      []
    case Nil{} Con{y, yt}:
      y <> yt
    case Con{x, xt} Nil{}:
      x <> xt
    case Con{x, xt} Con{y, yt}:
      pick(True{}, y, x) <> seq(xt, yt)

# the subtree's patch: the two children integrated (each computed alone,
# from the same base: a parallel call), then the node's own patch
def result(t: Node) -> List<&2, Maybe<&2, Nat>>:
  match t:
    case Leaf{i}:
      patch_of(i)
    case Split{+i, own, +l, +r}:
      a b = result(l) result(r)
      seq(overlay(overlay([], a, scope_of(info(l))), b, scope_of(info(r))), patch_of(i))

# one unit's bytes after a write
def land(w: Maybe<&2, Nat>, x: Nat) -> Nat:
  match w:
    case None{}:
      x
    case Some{y}:
      y

# the files with a patch applied
def apply(f: List<&2, Nat>, p: List<&2, Maybe<&2, Nat>>) -> List<&2, Nat>:
  match f p:
    case Nil{} Nil{}:
      []
    case Nil{} Con{y, yt}:
      []
    case Con{x, xt} Nil{}:
      x <> xt
    case Con{x, xt} Con{y, yt}:
      land(y, x) <> apply(xt, yt)

# Scheduling
# ----------

# what a node can do now: a user message waits, children's results
# arrived and not integrated, own-scope work left
type View is Data:
  View{message: Bool, arrived: Nat, own_work: Bool}

type Action is Data:
  ReadMessage{}
  Integrate{}
  WorkOwn{}
  Waits{}

def next_work(w: Bool) -> Action:
  match w:
    case True{}:
      WorkOwn{}
    case False{}:
      Waits{}

def next_arrived(n: Nat, w: Bool) -> Action:
  match n:
    case 0n:
      next_work(w)
    case 1n+p:
      Integrate{}

# the node's next action: the user's message first, then integration,
# then its own work; it waits only with nothing to do
def next(v: View) -> Action:
  match v:
    case View{m, n, w}:
      match m:
        case True{}:
          ReadMessage{}
        case False{}:
          next_arrived(n, w)
