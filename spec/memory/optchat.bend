# memory (spec): what the laws of area optchat (laws/optchat.bend) speak
# of, over the model in bend/optchat/ (Taelin's OptChat gist): Tiles,
# Merged, Summarized, Before, Prefix. A spec: the shipped code never
# calls it. The proofs in proof/optchat/ use it too.

import Base
import ../../bend/optchat/bits.bend as OBits
import ../../bend/optchat/node.bend as ONode
import ../../bend/optchat/info.bend as OInfo
import ../../bend/optchat/fit.bend as OFit
import ../../bend/optchat/state.bend as OState
import ../../bend/optchat/step.bend as OStep
import ../../bend/optchat/ctx.bend as OCtx

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

# every line of v ends by message b (in binary), and is built
def Before(+info: OInfo.Info, +b: List<&2, Bool>, v: List<&2, ONode.Node>) -> Type:
  match v:
    case Nil{}:
      Unit
    case +h <> t:
      ({OBits.Bits.le(OCtx.Node.end_bits(h), b) == True{} : Bool} & ({OInfo.Info.built(info, h) == True{} : Bool} & Before(info, b, t)))

# p is a prefix of v
def Prefix(p: List<&2, ONode.Node>, v: List<&2, ONode.Node>) -> Type:
  match p v:
    case Nil{} _:
      Unit
    case +x <> pr Nil{}:
      Empty
    case +x <> pr +y <> vr:
      ({x == y : ONode.Node} & Prefix(pr, vr))

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

# every line of v has an index without a high zero bit
def Canon(v: List<&2, ONode.Node>) -> Bool:
  match v:
    case Nil{}:
      True{}
    case ONode.Node{l, i} <> rest:
      Bool.and(Bits.canon(i), Canon(rest))

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
# The planner's replies to the chat's queries and its busy set after a
# call starts, is freed or a turn waits, restated from the gist (§4: the
# work queue, a compaction's view) and LAWS.bend H2 without the code of
# bend/optchat/queue.bend and ctx.bend. Node indices count by their
# value (OBits.Bits.val, pinned by optchat_bits_of).

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
# the ready merges wait (LAWS.bend H2.1)
def need(+cfg: OState.Cfg, +s: OState.St) -> List<&2, ONode.Node>:
  take(queue.room(cfg, s), queue.lines(OState.St.info(s), OState.St.busy(s), OState.Cfg.jobs(cfg), OState.St.view(s), 0n))

# A compaction's view (gist §4): the compaction view's lines that end by
# the node's bound, from the first on, stopping at the first line that
# does not or is unbuilt. A message's node is bounded by the message
# (the lines before it); a merge's by its last message.

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

def upto.keep(k: Bool, h: ONode.Node, t: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match k:
    case True{}:
      h <> t
    case False{}:
      Nil{}

# the lines of v from the first on that end by b and are built
def upto(v: List<&2, ONode.Node>, +info: OInfo.Info, +b: Nat) -> List<&2, ONode.Node>:
  match v:
    case Nil{}:
      Nil{}
    case +h <> t:
      upto.keep(Bool.and(Nat.is_le(line_end(h), b), OInfo.Info.built(info, h)), h, upto(t, info, b))

# the view a compaction of node n sees
def ctx(+s: OState.St, +n: ONode.Node) -> List<&2, ONode.Node>:
  upto(OState.St.cview(s), OState.St.info(s), ctx_bound(n))

# The calls: a node whose call starts is busy once; a freed or built
# node is not; a turn that starts to wait stops every busy node it does
# not need: it keeps the view's lines still unbuilt.

def with_busy(s: OState.St, bs: List<&2, ONode.Node>) -> OState.St:
  match s:
    case OState.St{t, info, view, shrink, cview, ready, busy}:
      OState.St{t, info, view, shrink, cview, ready, bs}

# busy with n, once
def busy_add(+busy: List<&2, ONode.Node>, +n: ONode.Node) -> List<&2, ONode.Node>:
  keep(Bool.not(member(busy, n)), n, busy)

# busy without n
def busy_del(busy: List<&2, ONode.Node>, +n: ONode.Node) -> List<&2, ONode.Node>:
  match busy:
    case Nil{}:
      Nil{}
    case +h <> t:
      keep(Bool.not(same(h, n)), h, busy_del(t, n))

# the busy nodes a waiting turn needs: the view's lines still unbuilt
def needed(+info: OInfo.Info, +view: List<&2, ONode.Node>, busy: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match busy:
    case Nil{}:
      Nil{}
    case +b <> t:
      keep(Bool.and(member(view, b), Bool.not(OInfo.Info.built(info, b))), b, needed(info, view, t))

# the chat once a turn starts to wait
def wait(s: OState.St) -> OState.St:
  match s:
    case OState.St{t, +info, +view, shrink, cview, ready, busy}:
      OState.St{t, info, view, shrink, cview, ready, needed(info, view, busy)}

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

# A message's batch and the compaction sawtooth (laws/optchat/queries.bend)
# --------------------------------------------------------------------------
# Gist §3.2 and LAWS.bend M1, without bend/optchat/fit.bend and step.bend:
# a line counts its node's bytes, or the placeholder's while unbuilt; a
# fit merges, while the view is over its budget, the most due pair of
# sibling lines whose parent is built (due = (T - last) / 2^l, compared
# cross-multiplied in numbers; of equally due pairs the oldest), at most
# once per line; past ceil a message's batch fits the view down to floor
# and the compaction view restarts from it down to cfloor, else the
# compaction view keeps its own sawtooth (past cceil, down to cfloor); a
# built node's parent is ready once its sibling is built and it is not.

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

def lvl(n: ONode.Node) -> Nat:
  match n:
    case ONode.Node{l, i}:
      l

def idx(n: ONode.Node) -> Nat:
  match n:
    case ONode.Node{l, i}:
      OBits.Bits.val(i)

# (u - xa) / 2^la > (u - xb) / 2^lb, both sides times 2^(la+lb), the
# subtractions moved across
def cross(+u: Nat, +la: Nat, +lb: Nat, xa: Nat, xb: Nat) -> Bool:
  Nat.is_gt(Nat.add(sh(lb, u), sh(la, xb)), Nat.add(sh(la, u), sh(lb, xa)))

# the pair from a on is more due than the pair from b on, at T messages:
# Last measures from one past the pair's last message ((i+2)·2^l, against
# T+1), First from its first message (i·2^l, against T)
def more_due(m: OFit.Age, +t: List<&2, Bool>, +a: ONode.Node, +b: ONode.Node) -> Bool:
  match m:
    case OFit.Last{}:
      cross(1n+OBits.Bits.val(t), lvl(a), lvl(b), sh(lvl(a), 2n+idx(a)), sh(lvl(b), 2n+idx(b)))
    case OFit.First{}:
      cross(OBits.Bits.val(t), lvl(a), lvl(b), sh(lvl(a), idx(a)), sh(lvl(b), idx(b)))

def best.vs(more: Bool, +a: ONode.Node, c: ONode.Node) -> ONode.Node:
  match more:
    case True{}:
      a
    case False{}:
      c

def best.take(+m: OFit.Age, +t: List<&2, Bool>, +a: ONode.Node, cur: Maybe<&2, ONode.Node>) -> Maybe<&2, ONode.Node>:
  match cur:
    case None{}:
      Some{a}
    case Some{+c}:
      Some{best.vs(more_due(m, t, a, c), a, c)}

def best.pick(ok: Bool, +m: OFit.Age, +t: List<&2, Bool>, +a: ONode.Node, cur: Maybe<&2, ONode.Node>) -> Maybe<&2, ONode.Node>:
  match ok:
    case False{}:
      cur
    case True{}:
      best.take(m, t, a, cur)

def best.pair(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, +a: ONode.Node, next: Maybe<&2, ONode.Node>, cur: Maybe<&2, ONode.Node>) -> Maybe<&2, ONode.Node>:
  match next:
    case None{}:
      cur
    case Some{b}:
      best.pick(mergeable(info, a, b), m, t, a, cur)

# the first line of the most due mergeable pair: a later pair wins only
# when strictly more due
def best.go(+m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, v: List<&2, ONode.Node>, cur: Maybe<&2, ONode.Node>) -> Maybe<&2, ONode.Node>:
  match v:
    case Nil{}:
      cur
    case +a <> +rest:
      best.go(m, t, info, rest, best.pair(m, t, info, a, List.head(&2, ONode.Node, rest), cur))

def merge.pick(hit: Bool, +x: ONode.Node, +y: ONode.Node, more: List<&2, ONode.Node>, rec: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match hit:
    case True{}:
      parent(x) <> more
    case False{}:
      x <> rec

def merge.here(+info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, rest: List<&2, ONode.Node>, rec: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match rest:
    case Nil{}:
      [x]
    case +y <> more:
      merge.pick(Bool.and(same(x, a), mergeable(info, x, y)), x, y, more, rec)

# the first pair (a, y) of v that may merge, replaced by its parent
def merge(+info: OInfo.Info, v: List<&2, ONode.Node>, +a: ONode.Node) -> List<&2, ONode.Node>:
  match v:
    case Nil{}:
      Nil{}
    case +x <> +rest:
      merge.here(info, a, x, rest, merge(info, rest, a))

def choose.if(over: Bool, +m: OFit.Age, +t: List<&2, Bool>, +info: OInfo.Info, v: List<&2, ONode.Node>) -> Maybe<&2, ONode.Node>:
  match over:
    case False{}:
      None{}
    case True{}:
      best.go(m, t, info, v, None{})

# the next merge: the most due pair, while over budget
def choose(+m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> Maybe<&2, ONode.Node>:
  choose.if(Nat.is_gt(vsize(ph, info, v), budget), m, t, info, v)

def fit.cons(n: ONode.Node, r: List<&2, ONode.Node> & List<&2, ONode.Node>) -> List<&2, ONode.Node> & List<&2, ONode.Node>:
  (ms, out) = r
  (n <> ms, out)

def fit.go(fuel: Nat, c: Maybe<&2, ONode.Node>, +m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> List<&2, ONode.Node> & List<&2, ONode.Node>:
  match fuel c:
    case 0n _:
      (Nil{}, v)
    case 1n+f None{}:
      (Nil{}, v)
    case 1n+f Some{+a}:
      +w = merge(info, v, a)
      fit.cons(parent(a), fit.go(f, choose(m, t, budget, ph, info, w), m, t, budget, ph, info, w))

# a fit of the view into budget bytes: the merged parents in merge order,
# and the view (each merge drops a line: the view's length bounds them)
def fit(+m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> List<&2, ONode.Node> & List<&2, ONode.Node>:
  fit.go(List.length(&2, ONode.Node, v), choose(m, t, budget, ph, info, v), m, t, budget, ph, info, v)

def fit.view(+m: OFit.Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, fit(m, t, budget, ph, info, v))

def fitc.if(over: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match over:
    case False{}:
      cv
    case True{}:
      fit.view(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, cv)

# the compaction view's sawtooth: past cceil, down to cfloor
def fitc(+cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  fitc.if(Nat.is_gt(vsize(OState.Cfg.ph(cfg), info, cv), OState.Cfg.cceil(cfg)), cfg, t, info, cv)

# T + 1, in binary (lowest bit first)
def inc(bs: List<&2, Bool>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      [True{}]
    case h <> t:
      match h:
        case False{}:
          True{} <> t
        case True{}:
          False{} <> inc(t)

def msg.cview(merged: List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match merged:
    case Nil{}:
      fitc(cfg, t, info, cv)
    case h <> rest:
      fit.view(OFit.Last{}, t, OState.Cfg.cfloor(cfg), OState.Cfg.ph(cfg), info, view)

def msg.batch(r: List<&2, ONode.Node> & List<&2, ONode.Node>, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +cv: List<&2, ONode.Node>, ready: List<&2, ONode.Node>, busy: List<&2, ONode.Node>) -> OState.St & List<&2, ONode.Node>:
  (merged0, view0) = r
  +merged = merged0
  +view = view0
  (OState.St{t, info, view, Nat.is_gt(vsize(OState.Cfg.ph(cfg), info, view), OState.Cfg.floor(cfg)), msg.cview(merged, cfg, t, info, view, cv), ready, busy}, merged)

def msg.go(grow: Bool, +cfg: OState.Cfg, +t: List<&2, Bool>, +info: OInfo.Info, +view: List<&2, ONode.Node>, +cv: List<&2, ONode.Node>, ready: List<&2, ONode.Node>, busy: List<&2, ONode.Node>) -> OState.St & List<&2, ONode.Node>:
  match grow:
    case False{}:
      (OState.St{t, info, view, False{}, fitc(cfg, t, info, cv), ready, busy}, Nil{})
    case True{}:
      msg.batch(fit(OFit.Last{}, t, OState.Cfg.floor(cfg), OState.Cfg.ph(cfg), info, view), cfg, t, info, cv, ready, busy)

# the view with message T's line
def grown(+s: OState.St) -> List<&2, ONode.Node>:
  List.append(&2, ONode.Node, OState.St.view(s), [ONode.Node{0n, OState.St.t(s)}])

# a batch runs (or goes on) at this message: still shrinking, or past ceil
def batch(+cfg: OState.Cfg, +s: OState.St) -> Bool:
  Bool.or(OState.St.shrink(s), Nat.is_gt(vsize(OState.Cfg.ph(cfg), OState.St.info(s), grown(s)), OState.Cfg.ceil(cfg)))

# message T arrives: the chat after it, and the batch's merged parents
def msg(+cfg: OState.Cfg, +s: OState.St) -> OState.St & List<&2, ONode.Node>:
  msg.go(batch(cfg, s), cfg, inc(OState.St.t(s)), OState.St.info(s), grown(s), List.append(&2, ONode.Node, OState.St.cview(s), [ONode.Node{0n, OState.St.t(s)}]), OState.St.ready(s), OState.St.busy(s))

# the index with its lowest bit flipped (no high zero bit kept)
def flip(bs: List<&2, Bool>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      [True{}]
    case h <> t:
      match h:
        case False{}:
          True{} <> t
        case True{}:
          match t:
            case Nil{}:
              Nil{}
            case x <> r:
              False{} <> x <> r

# the other half of n's parent
def sibling(n: ONode.Node) -> ONode.Node:
  match n:
    case ONode.Node{l, i}:
      ONode.Node{l, flip(i)}

# a before b: by level, then index
def before(a: ONode.Node, b: ONode.Node) -> Bool:
  match a b:
    case ONode.Node{+la, ia} ONode.Node{+lb, ib}:
      Bool.or(Nat.is_lt(la, lb), Bool.and(Nat.is_eq(la, lb), Nat.is_lt(OBits.Bits.val(ia), OBits.Bits.val(ib))))

def ins.at(here: Bool, dup: Bool, +x: ONode.Node, +h: ONode.Node, t: List<&2, ONode.Node>, rec: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match here dup:
    case True{} _:
      x <> h <> t
    case False{} True{}:
      h <> t
    case False{} False{}:
      h <> rec

# x into the sorted xs, once
def ins(xs: List<&2, ONode.Node>, +x: ONode.Node) -> List<&2, ONode.Node>:
  match xs:
    case Nil{}:
      [x]
    case +h <> +t:
      ins.at(before(x, h), same(x, h), x, h, t, ins(t, x))

def ready.if(go: Bool, +p: ONode.Node, rs: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match go:
    case False{}:
      rs
    case True{}:
      ins(rs, p)

# n is built: its parent is ready once its sibling is built and it is not
def ready_note(+info: OInfo.Info, +n: ONode.Node, rs: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  ready.if(Bool.and(OInfo.Info.built(info, sibling(n)), Bool.not(OInfo.Info.built(info, parent(n)))), parent(n), rs)

def build.go(+cfg: OState.Cfg, +n: ONode.Node, +info: OInfo.Info, s: OState.St) -> OState.St:
  match s:
    case OState.St{+t, i0, view, shrink, cview, ready, busy}:
      OState.St{t, info, view, shrink, fitc(cfg, t, info, cview), ready_note(info, n, busy_del(ready, n)), busy_del(busy, n)}

# node n is built, size bytes: its size is noted, the compaction view keeps
# its sawtooth, n is no longer ready nor busy, its parent may be ready
def build(+cfg: OState.Cfg, +s: OState.St, +n: ONode.Node, +size: Nat) -> OState.St:
  build.go(cfg, n, OInfo.Info.set(OState.St.info(s), n, size), s)
