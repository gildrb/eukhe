# memory (spec): what the laws of area optchat (laws/optchat.bend) speak
# of, over the model in bend/optchat/ (Taelin's OptChat gist): Tiles,
# Merged, Summarized, Prefix, starts_before; and what the planner answers
# (CtxOf, Chain, Saw, count, copies, Sorted). A spec: the shipped
# code never calls it. The proofs in proof/optchat/ use it too.

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep

# What the laws speak of
# ----------------------

# Tiles(s, v, e): the lines of v cover the messages s..e-1, each message
# once, contiguous, oldest first. A line is a tree node: node(l, i)
# covers the 2^l messages from i·2^l on.
def Tiles(s: Nat, v: List<&2, ONode.Node>, e: Nat) -> Type:
  match v:
    case Nil{}:
      {s == e : Nat}
    case +h <> t:
      ({ONode.Node.start(h) == s : Nat} & Tiles(Nat.add(s, ONode.Node.count(h)), t, e))

# Here(info, x, rest, z, w): x and the first line of rest are the two
# halves of a built parent z, and w is the rest after them
def Here(+info: OInfo.Info, +x: ONode.Node, rest: List<&2, ONode.Node>, +z: ONode.Node, +w: List<&2, ONode.Node>) -> Type:
  match rest:
    case Nil{}:
      Empty
    case +y <> more:
      ({OFit.mergeable(info, x, y) == True{} : Bool} & ({z == ONode.Node.parent(x) : ONode.Node} & {w == more : List<&2, ONode.Node>}))

# Merged(info, v, w): w is v with one pair of sibling lines replaced by
# their built parent, and nothing else changed
def Merged(+info: OInfo.Info, v: List<&2, ONode.Node>, w: List<&2, ONode.Node>) -> Type:
  match v w:
    case Nil{} _:
      Empty
    case +x <> vr Nil{}:
      Empty
    case +x <> +vr +z <> +wr:
      Or(Here(info, x, vr, z, wr), ({x == z : ONode.Node} & Merged(info, vr, wr)))

# some pair of adjacent lines may merge (its parent is built)
def can_merge(+info: OInfo.Info, v: List<&2, ONode.Node>) -> Bool:
  match v:
    case Nil{}:
      False{}
    case +x <> +rest:
      Bool.or(OFit.pair.ok(info, x, List.head(&2, ONode.Node, rest)), can_merge(info, rest))

# every node of v is built
def Built(+info: OInfo.Info, v: List<&2, ONode.Node>) -> Type:
  match v:
    case Nil{}:
      Unit
    case +h <> t:
      ({OInfo.Info.built(info, h) == True{} : Bool} & Built(info, t))

# every line of v that merges messages (level above 0) is built; a
# message's own line may wait for its summary
def Summarized(+info: OInfo.Info, v: List<&2, ONode.Node>) -> Type:
  match v:
    case Nil{}:
      Unit
    case +h <> t:
      ({OBits.Bool.implies(OBits.Nat.is_pos(ONode.Node.lvl(h)), OInfo.Info.built(info, h)) == True{} : Bool} & Summarized(info, t))

# p is a prefix of v
def Prefix(p: List<&2, ONode.Node>, v: List<&2, ONode.Node>) -> Type:
  match p v:
    case Nil{} _:
      Unit
    case +x <> pr Nil{}:
      Empty
    case +x <> pr +y <> vr:
      ({x == y : ONode.Node} & Prefix(pr, vr))

# every node of ns starts before message due (the due mark)
def starts_before(+due: Nat, ns: List<&2, ONode.Node>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(Nat.is_lt(ONode.Node.start(h), due), starts_before(due, t))

# bs has no high zero bit (as Bits.inc and Bits.up make bits): its last
# bit, if any, is True
def Bits.canon.go(t: List<&2, Bool>, h: Bool) -> Bool:
  match t:
    case Nil{}:
      h
    case x <> r:
      Bits.canon.go(r, x)

def Bits.canon(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      True{}
    case h <> t:
      Bits.canon.go(t, h)

def view.of(+cfg: OState.Cfg, +evs: List<&2, OState.Ev>) -> List<&2, ONode.Node>:
  OState.St.view(OStep.run(cfg, evs))

def cview.of(+cfg: OState.Cfg, +evs: List<&2, OState.Ev>) -> List<&2, ONode.Node>:
  OState.St.cview(OStep.run(cfg, evs))

def total.of(+cfg: OState.Cfg, +evs: List<&2, OState.Ev>) -> Nat:
  OBits.Bits.val(OState.St.t(OStep.run(cfg, evs)))

def ten() -> List<&2, Bool>:
  [False{}, True{}, False{}, True{}]

def view10() -> List<&2, ONode.Node>:
  [ONode.Node{2n, []}, ONode.Node{2n, [True{}]}, ONode.Node{0n, [False{}, False{}, False{}, True{}]}, ONode.Node{0n, [True{}, False{}, False{}, True{}]}]

# What the planner answers (laws/optchat/queries.bend)
# -----------------------------------------------------
# The planner's replies to the chat's queries and its moves on each
# event, restated from the gist (§3.2: a message's batch; §4: the work
# queue, a compaction's view) and spec/README.md M1 without the code of
# bend/optchat/. Node indices count by their value (OBits.Bits.val,
# pinned by optchat_bits_of).

# a and b name one node: one level, one index
def same(a: ONode.Node, b: ONode.Node) -> Bool:
  match a b:
    case ONode.Node{la, ia} ONode.Node{lb, ib}:
      Bool.and(Nat.is_eq(la, lb), Nat.is_eq(OBits.Bits.val(ia), OBits.Bits.val(ib)))

# x is one of xs
def member(xs: List<&2, ONode.Node>, +x: ONode.Node) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(same(h, x), member(t, x))

def keep(k: Bool, h: ONode.Node, t: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match k:
    case True{}:
      h <> t
    case False{}:
      t

# the first n of xs
def take(n: Nat, xs: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      match xs:
        case Nil{}:
          Nil{}
        case x <> t:
          x <> take(k, t)

# The work queue (gist §4): a message's line starts once fewer than jobs
# lines before it in the view are unbuilt; a merge starts once it is
# ready (both halves built); a running node does not start again; at
# most jobs calls run at once.

# a line that is unbuilt counts 1
def unbuilt(b: Bool) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      1n

# the view's lines that may start, oldest first: unbuilt, not running,
# with fewer than jobs unbuilt lines before them (u so far)
def queue.lines(+info: OInfo.Info, +busy: List<&2, ONode.Node>, +jobs: Nat, v: List<&2, ONode.Node>, +u: Nat) -> List<&2, ONode.Node>:
  match v:
    case Nil{}:
      Nil{}
    case +h <> t:
      +b = OInfo.Info.built(info, h)
      keep(Bool.and(Bool.not(Nat.is_ge(u, jobs)), Bool.and(Bool.not(b), Bool.not(member(busy, h)))), h, queue.lines(info, busy, jobs, t, Nat.add(u, unbuilt(b))))

# the ready merges not running, in their order
def queue.ready(+busy: List<&2, ONode.Node>, rs: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match rs:
    case Nil{}:
      Nil{}
    case +h <> t:
      keep(Bool.not(member(busy, h)), h, queue.ready(busy, t))

# the free job slots
def queue.room(+cfg: OState.Cfg, +s: OState.St) -> Nat:
  Nat.sub(OState.Cfg.jobs(cfg), List.length(&2, ONode.Node, OState.St.busy(s)))

# the nodes to start: the view's lines that may start, then the ready
# merges, as many as the free slots
def cands(+cfg: OState.Cfg, +s: OState.St) -> List<&2, ONode.Node>:
  take(queue.room(cfg, s), List.append(&2, ONode.Node, queue.lines(OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), OState.St.view(s), 0n), queue.ready(OState.St.busy(s), OState.St.ready(s))))

# the nodes to start while a turn waits for the view: its lines only,
# the ready merges wait (spec/README.md M1: a
# turn never waits forever on memory)
def need(+cfg: OState.Cfg, +s: OState.St) -> List<&2, ONode.Node>:
  take(queue.room(cfg, s), queue.lines(OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), OState.St.view(s), 0n))

# A compaction's view (gist §4)
# -----------------------------
# A message's compaction sees the compaction view's lines that end by the
# message; a merge's those that end by its last message; from the first
# line on, up to the first line that does not end by then or is not
# built yet.

# x·2^l
def sh(l: Nat, x: Nat) -> Nat:
  match l:
    case 0n:
      x
    case 1n+p:
      Nat.double(sh(p, x))

# one past the last message of node(l, i): (i+1)·2^l
def line_end(n: ONode.Node) -> Nat:
  match n:
    case ONode.Node{l, i}:
      sh(l, 1n+OBits.Bits.val(i))

# the bound of a compaction of node(l, i): i for a message, else (i+1)·2^l
def ctx_bound(n: ONode.Node) -> Nat:
  match n:
    case ONode.Node{l, i}:
      match l:
        case 0n:
          OBits.Bits.val(i)
        case 1n+p:
          sh(1n+p, 1n+OBits.Bits.val(i))

# the line x may be shown to a compaction bounded by b: it is built and
# ends by message b
def shown(+info: OInfo.Info, +b: Nat, +x: ONode.Node) -> Bool:
  Bool.and(Nat.is_le(line_end(x), b), OInfo.Info.built(info, x))

# CtxOf(info, b, c, v): c is the longest start of v whose every line may
# be shown under b: c is a prefix of v, each of its lines is shown, and
# the line of v right after it, if any, is not
def CtxOf(+info: OInfo.Info, +b: Nat, c: List<&2, ONode.Node>, v: List<&2, ONode.Node>) -> Type:
  match c v:
    case Nil{} Nil{}:
      Unit
    case Nil{} +y <> vr:
      {shown(info, b, y) == False{} : Bool}
    case +x <> cr Nil{}:
      Empty
    case +x <> cr +y <> vr:
      ({x == y : ONode.Node} & ({shown(info, b, x) == True{} : Bool} & CtxOf(info, b, cr, vr)))

# The calls
# ---------

def with_busy(s: OState.St, bs: List<&2, ONode.Node>) -> OState.St:
  match s:
    case OState.St{t, info, view, shrink, cview, ready, busy}:
      OState.St{t, info, view, shrink, cview, ready, bs}

# n + 1 when b holds
def one_if(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

# 0 when b holds, else n
def zero_if(b: Bool, n: Nat) -> Nat:
  match b:
    case True{}:
      0n
    case False{}:
      n

# how many lines of xs name the node x (by level and index value)
def count(xs: List<&2, ONode.Node>, +x: ONode.Node) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      one_if(same(h, x), count(t, x))

# The built nodes' sizes: a map from a node (its level and its index
# bits, exactly as the model holds them) to its size.

def bit_same(x: Bool, y: Bool) -> Bool:
  match x:
    case True{}:
      y
    case False{}:
      Bool.not(y)

# two indices have the same bits
def bits_same(a: List<&2, Bool>, b: List<&2, Bool>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> ys:
      False{}
    case x <> xs Nil{}:
      False{}
    case x <> xs y <> ys:
      Bool.and(bit_same(x, y), bits_same(xs, ys))

# n and m are one key of the map
def key_same(n: ONode.Node, m: ONode.Node) -> Bool:
  match n m:
    case ONode.Node{l, i} ONode.Node{k, j}:
      Bool.and(Nat.is_eq(l, k), bits_same(i, j))

def info_pick(hit: Bool, z: Nat, old: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{z}
    case False{}:
      old

# the size of node m once node n is built with z bytes, m having had old
def info_after(n: ONode.Node, z: Nat, m: ONode.Node, old: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  info_pick(key_same(n, m), z, old)

# the sizes are a map of the nodes built (a chat's), not the push
# comparison's All (every node built, one size)
def is_map(info: OInfo.Info) -> Bool:
  match info:
    case OInfo.All{z}:
      False{}
    case OInfo.Lvls{ts}:
      True{}

# how many lines of xs are exactly the node x (level and index bits: the
# key the built sizes are read by)
def copies(xs: List<&2, ONode.Node>, +x: ONode.Node) -> Nat:
  match xs:
    case Nil{}:
      0n
    case h <> t:
      one_if(key_same(h, x), copies(t, x))

# The ready merges: a list by level, then index value, each once.

# a before b: by level, then index value
def before(a: ONode.Node, b: ONode.Node) -> Bool:
  match a b:
    case ONode.Node{+la, ia} ONode.Node{+lb, ib}:
      Bool.or(Nat.is_lt(la, lb), Bool.and(Nat.is_eq(la, lb), Nat.is_lt(OBits.Bits.val(ia), OBits.Bits.val(ib))))

def Sorted.go(xs: List<&2, ONode.Node>, +p: ONode.Node) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +h <> t:
      Bool.and(before(p, h), Sorted.go(t, h))

# every node of xs comes strictly before the next
def Sorted(xs: List<&2, ONode.Node>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case +h <> t:
      Sorted.go(t, h)

# The tree
# --------

# an index halved, and its lowest bit
def half(i: List<&2, Bool>) -> List<&2, Bool>:
  match i:
    case Nil{}:
      Nil{}
    case h <> t:
      t

def low(i: List<&2, Bool>) -> Bool:
  match i:
    case Nil{}:
      False{}
    case h <> t:
      h

# node(l+1, i/2)
def parent(n: ONode.Node) -> ONode.Node:
  match n:
    case ONode.Node{l, i}:
      ONode.Node{1n+l, half(i)}

# a and b are the two halves of one parent, a first
def sib(a: ONode.Node, b: ONode.Node) -> Bool:
  match a b:
    case ONode.Node{la, +ia} ONode.Node{lb, +ib}:
      Bool.and(Nat.is_eq(la, lb), Bool.and(Bool.not(low(ia)), Bool.and(low(ib), bits_same(half(ia), half(ib)))))

# a and b may merge: siblings with a built parent
def mergeable(+info: OInfo.Info, +a: ONode.Node, +b: ONode.Node) -> Bool:
  Bool.and(sib(a, b), OInfo.Info.built(info, parent(a)))

def pair_ok(+info: OInfo.Info, +a: ONode.Node, next: Maybe<&2, ONode.Node>) -> Bool:
  match next:
    case None{}:
      False{}
    case Some{b}:
      mergeable(info, a, b)

# some line of v and the next may merge
def mergeable_any(+info: OInfo.Info, v: List<&2, ONode.Node>) -> Bool:
  match v:
    case Nil{}:
      False{}
    case +x <> +rest:
      Bool.or(pair_ok(info, x, List.head(&2, ONode.Node, rest)), mergeable_any(info, rest))

# the other half of k's parent: k + 1 for an even k, k - 1 for an odd one
def other.of(odd: Bool, k: Nat) -> Nat:
  match odd:
    case True{}:
      Nat.sub(k, 1n)
    case False{}:
      1n+k

def other(+k: Nat) -> Nat:
  other.of(Nat.is_eq(Nat.mod(k, 2n), 1n), k)

def lvl(n: ONode.Node) -> Nat:
  match n:
    case ONode.Node{l, i}:
      l

def idx(n: ONode.Node) -> Nat:
  match n:
    case ONode.Node{l, i}:
      OBits.Bits.val(i)

# A message's batch and the compaction sawtooth (gist §3.2, §4)
# -------------------------------------------------------------
# A line counts its node's bytes, or the placeholder's while unbuilt. A
# fit merges, while the view is over its budget, the most due pair of
# sibling lines whose parent is built: due = (T - last) / 2^l, l the
# lines' level, last the pair's last message; of equally due pairs the
# oldest. Past ceil a message's batch fits the view down to floor and the
# compaction view restarts from it down to cfloor; else the compaction
# view keeps its own sawtooth (past cceil, down to cfloor).

def size_of(+ph: Nat, m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      ph
    case Some{z}:
      z

# the view's bytes
def vsize(+ph: Nat, +info: OInfo.Info, v: List<&2, ONode.Node>) -> Nat:
  match v:
    case Nil{}:
      0n
    case +h <> t:
      Nat.add(size_of(ph, OInfo.Info.get(info, h)), vsize(ph, info, t))

# (u - xa) / 2^la > (u - xb) / 2^lb as rationals: both sides times
# 2^(la+lb), the subtractions moved across (so no Nat subtraction cuts)
def cross(+u: Nat, +la: Nat, +lb: Nat, xa: Nat, xb: Nat) -> Bool:
  Nat.is_gt(Nat.add(sh(lb, u), sh(la, xb)), Nat.add(sh(la, u), sh(lb, xa)))

# the pair from a on is strictly more due than the pair from b on, at T
# messages (t): Last measures from one past the pair's last message
# ((i+2)·2^l, against T+1), First from its first message (i·2^l,
# against T)
def more_due(m: OFit.Age, +t: List<&2, Bool>, +a: ONode.Node, +b: ONode.Node) -> Bool:
  match m:
    case OFit.Last{}:
      cross(1n+OBits.Bits.val(t), lvl(a), lvl(b), sh(lvl(a), 2n+idx(a)), sh(lvl(b), 2n+idx(b)))
    case OFit.First{}:
      cross(OBits.Bits.val(t), lvl(a), lvl(b), sh(lvl(a), idx(a)), sh(lvl(b), idx(b)))

# no pair of ys that may merge (a line and the next) is more due than the
# pair from a on
def NoneMore(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +a: ONode.Node, ys: List<&2, ONode.Node>) -> Type:
  match ys:
    case Nil{}:
      Unit
    case +y <> +r:
      ({OBits.Bool.implies(pair_ok(info, y, List.head(&2, ONode.Node, r)), Bool.not(more_due(m, t, y, a))) == True{} : Bool} & NoneMore(m, t, info, a, r))

# x is a, x and the next line y may merge, w is v after them, and no
# pair from y on is more due
def At.here(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, rest: List<&2, ONode.Node>, +z: ONode.Node, +w: List<&2, ONode.Node>) -> Type:
  match rest:
    case Nil{}:
      Empty
    case +y <> +more:
      ({x == a : ONode.Node} & ({mergeable(info, x, y) == True{} : Bool} & ({z == parent(x) : ONode.Node} & ({w == more : List<&2, ONode.Node>} & NoneMore(m, t, info, a, y <> more)))))

# At(m, t, info, a, v, w): w is v with the pair of lines from a on (a and
# the next line, siblings whose parent is built) replaced by their parent,
# and nothing else changed; every pair before it that may merge is
# strictly less due, none after it more due (of equally due pairs, the
# oldest merges)
def At(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +a: ONode.Node, v: List<&2, ONode.Node>, w: List<&2, ONode.Node>) -> Type:
  match v w:
    case Nil{} _:
      Empty
    case +x <> vr Nil{}:
      Empty
    case +x <> +vr +z <> +wr:
      Or(At.here(m, t, info, a, x, vr, z, wr), ({x == z : ONode.Node} & ({OBits.Bool.implies(pair_ok(info, x, List.head(&2, ONode.Node, vr)), more_due(m, t, a, x)) == True{} : Bool} & At(m, t, info, a, vr, wr))))

# a fit may stop at v: within its budget, or no pair of lines may merge
def Stop(+info: OInfo.Info, +budget: Nat, +ph: Nat, +v: List<&2, ONode.Node>) -> Type:
  Or({Nat.is_le(vsize(ph, info, v), budget) == True{} : Bool}, {mergeable_any(info, v) == False{} : Bool})

# Chain(m, t, info, budget, ph, v, ms, w): the fit of v into budget bytes
# merges the parents ms, in order, and ends at w: each merge, made while
# the view is over budget, replaces the most due pair (At) by its parent;
# the view then stops (Stop)
def Chain(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +budget: Nat, +ph: Nat, +v: List<&2, ONode.Node>, ms: List<&2, ONode.Node>, +w: List<&2, ONode.Node>) -> Type:
  match ms:
    case Nil{}:
      ({w == v : List<&2, ONode.Node>} & Stop(info, budget, ph, v))
    case +p <> rest:
      ({Nat.is_gt(vsize(ph, info, v), budget) == True{} : Bool} & (&u: List<&2, ONode.Node> -> (&a: ONode.Node -> (({parent(a) == p : ONode.Node} & At(m, t, info, a, v, u)) & Chain(m, t, info, budget, ph, u, rest, w)))))

# Fitted(m, t, info, budget, ph, v, w): some fit of v into budget ends at w
def Fitted(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +budget: Nat, +ph: Nat, +v: List<&2, ONode.Node>, +w: List<&2, ONode.Node>) -> Type:
  &ms: List<&2, ONode.Node> -> Chain(m, t, info, budget, ph, v, ms, w)

def Saw.if(over: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, +w: List<&2, ONode.Node>) -> Type:
  match over:
    case False{}:
      {w == cv : List<&2, ONode.Node>}
    case True{}:
      Fitted(OFit.Last{}, t, info, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), cv, w)

# Saw(cfg, t, info, cv, w): the compaction view's sawtooth takes cv to w:
# past cceil, cv is fitted down to cfloor; else it stays
def Saw(+cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, +w: List<&2, ONode.Node>) -> Type:
  Saw.if(Nat.is_gt(vsize(OState.Cfg.ph(cfg), info, cv), OState.Cfg.cceil(cfg)), cfg, t, info, cv, w)

# the view with message T's line
def grown(+s: OState.St) -> List<&2, ONode.Node>:
  List.append(&2, ONode.Node, OState.St.view(s), [ONode.Node{0n, OState.St.t(s)}])

# the compaction view with message T's line
def cgrown(+s: OState.St) -> List<&2, ONode.Node>:
  List.append(&2, ONode.Node, OState.St.cview(s), [ONode.Node{0n, OState.St.t(s)}])

# a batch runs (or goes on) at this message: still shrinking, or past ceil
def batch(+cfg: OState.Cfg, +s: OState.St) -> Bool:
  Bool.or(OState.St.shrink(s), Nat.is_gt(vsize(OState.Cfg.ph(cfg), OState.St.info(s), grown(s)), OState.Cfg.ceil(cfg)))

# the compaction view after a batch that merged ms: restarted from the new
# view w, fitted down to cfloor; after a batch that merged nothing, the
# sawtooth of the compaction view with the message's line, cv
def Restart(ms: List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +w: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>, +c: List<&2, ONode.Node>) -> Type:
  match ms:
    case Nil{}:
      Saw(cfg, t, info, cv, c)
    case h <> r:
      Fitted(OFit.Last{}, t, info, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), w, c)
