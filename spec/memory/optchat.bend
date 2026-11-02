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
