# optchat: the reference batch: line sizes, the due measure, the most due mergeable pair, merging until the view fits

import Base
import ./bits.bend as OBits
import ./node.bend as ONode
import ./info.bend as OInfo

# Sizes
# -----
# A line counts its node's bytes, or the placeholder's while its message
# is not summarized yet (only a message's own line can be unbuilt).

def size.of(+ph: Nat, m: Maybe<&2, Nat>) -> Nat:
  match m:
    case None{}:
      ph
    case Some{s}:
      s

def line_size(+ph: Nat, +info: OInfo.Info, +n: ONode.Node) -> Nat:
  size.of(ph, OInfo.Info.get(info, n))

def view_size(+ph: Nat, +info: OInfo.Info, v: List<&2, ONode.Node>) -> Nat:
  match v:
    case Nil{}:
      0n
    case h <> t:
      Nat.add(line_size(ph, info, h), view_size(ph, info, t))

# Due
# ---
# A pair of sibling lines (l, i), (l, i+1) is due (T - last) / 2^l: how
# long ago it ended, in its own line size (gist §3.2). First measures from
# the pair's first message instead, the gist's known mistake.

type Age is Data:
  Last{}
  First{}

# e: one past the pair's last message, (i+2)·2^l; s: its first, i·2^l
def pair_end(+a: ONode.Node) -> List<&2, Bool>:
  match a:
    case ONode.Node{l, i}:
      OBits.Bits.shl(l, OBits.Bits.inc(OBits.Bits.inc(i)))

def pair_start(+a: ONode.Node) -> List<&2, Bool>:
  match a:
    case ONode.Node{l, i}:
      OBits.Bits.shl(l, i)

# the pair from a on is more due than the pair from b on:
#   Last:  (T - last_a) / 2^la  >  (T - last_b) / 2^lb
#   First: (T - first_a) / 2^la >  (T - first_b) / 2^lb
# Both sides times 2^(la+lb), and T - last = T+1 - e, moved across:
#   Last:  (T+1)·2^lb + e_b·2^la  >  (T+1)·2^la + e_a·2^lb
#   First:     T·2^lb + s_b·2^la  >      T·2^la + s_a·2^lb
def more_due.cross(+u: List<&2, Bool>, +la: Nat, +lb: Nat, xa: List<&2, Bool>, xb: List<&2, Bool>) -> Bool:
  OBits.Bits.gt(OBits.Bits.add(OBits.Bits.shl(lb, u), OBits.Bits.shl(la, xb)), OBits.Bits.add(OBits.Bits.shl(la, u), OBits.Bits.shl(lb, xa)))

def more_due(m: Age, +t: List<&2, Bool>, +a: ONode.Node, +b: ONode.Node) -> Bool:
  match m:
    case Last{}:
      more_due.cross(OBits.Bits.inc(t), ONode.Node.lvl(a), ONode.Node.lvl(b), pair_end(a), pair_end(b))
    case First{}:
      more_due.cross(t, ONode.Node.lvl(a), ONode.Node.lvl(b), pair_start(a), pair_start(b))

# a and b may merge: they are the halves of a built parent
def mergeable(+info: OInfo.Info, +a: ONode.Node, +b: ONode.Node) -> Bool:
  Bool.and(ONode.Node.sib(a, b), OInfo.Info.built(info, ONode.Node.parent(a)))

# a and the next line (if any) may merge
def pair.ok(+info: OInfo.Info, +a: ONode.Node, next: Maybe<&2, ONode.Node>) -> Bool:
  match next:
    case None{}:
      False{}
    case Some{b}:
      mergeable(info, a, b)

def best.vs(more: Bool, +a: ONode.Node, c: ONode.Node) -> ONode.Node:
  match more:
    case True{}:
      a
    case False{}:
      c

def best.take(+m: Age, +t: List<&2, Bool>, +a: ONode.Node, cur: Maybe<&2, ONode.Node>) -> Maybe<&2, ONode.Node>:
  match cur:
    case None{}:
      Some{a}
    case Some{+c}:
      Some{best.vs(more_due(m, t, a, c), a, c)}

def best.pick(ok: Bool, +m: Age, +t: List<&2, Bool>, +a: ONode.Node, cur: Maybe<&2, ONode.Node>) -> Maybe<&2, ONode.Node>:
  match ok:
    case False{}:
      cur
    case True{}:
      best.take(m, t, a, cur)

def best.pair(+m: Age, +t: List<&2, Bool>, +info: OInfo.Info, +a: ONode.Node, next: Maybe<&2, ONode.Node>, cur: Maybe<&2, ONode.Node>) -> Maybe<&2, ONode.Node>:
  match next:
    case None{}:
      cur
    case Some{b}:
      best.pick(mergeable(info, a, b), m, t, a, cur)

# scan the pairs oldest first; a later pair wins only when strictly more
# due, so of equal pairs the oldest stays. cur is the first line of the
# most due pair so far.
def best.go(+m: Age, +t: List<&2, Bool>, +info: OInfo.Info, v: List<&2, ONode.Node>, cur: Maybe<&2, ONode.Node>) -> Maybe<&2, ONode.Node>:
  match v:
    case Nil{}:
      cur
    case +a <> +rest:
      best.go(m, t, info, rest, best.pair(m, t, info, a, List.head(&2, ONode.Node, rest), cur))

# the first line of the most due mergeable pair, if any; t is T, the
# number of messages, in binary
def best(+m: Age, +t: List<&2, Bool>, +info: OInfo.Info, v: List<&2, ONode.Node>) -> Maybe<&2, ONode.Node>:
  best.go(m, t, info, v, None{})

# Merging
# -------

def merge.pick(hit: Bool, +x: ONode.Node, +y: ONode.Node, more: List<&2, ONode.Node>, rec: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match hit:
    case True{}:
      ONode.Node.parent(x) <> more
    case False{}:
      x <> rec

def merge.here(+info: OInfo.Info, +a: ONode.Node, +x: ONode.Node, rest: List<&2, ONode.Node>, rec: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  match rest:
    case Nil{}:
      [x]
    case +y <> more:
      merge.pick(Bool.and(ONode.Node.eq(x, a), mergeable(info, x, y)), x, y, more, rec)

# the first pair (a, y) of v that may merge, replaced by its parent
def merge(+info: OInfo.Info, v: List<&2, ONode.Node>, +a: ONode.Node) -> List<&2, ONode.Node>:
  match v:
    case Nil{}:
      Nil{}
    case +x <> +rest:
      merge.here(info, a, x, rest, merge(info, rest, a))

def choose.if(over: Bool, +m: Age, +t: List<&2, Bool>, +info: OInfo.Info, v: List<&2, ONode.Node>) -> Maybe<&2, ONode.Node>:
  match over:
    case False{}:
      None{}
    case True{}:
      best(m, t, info, v)

# the next merge of a fit: the most due pair, while over budget
def choose(+m: Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> Maybe<&2, ONode.Node>:
  choose.if(Nat.is_gt(view_size(ph, info, v), budget), m, t, info, v)

def fit.cons(n: ONode.Node, r: List<&2, ONode.Node> & List<&2, ONode.Node>) -> List<&2, ONode.Node> & List<&2, ONode.Node>:
  (ms, out) = r
  (n <> ms, out)

# merge the most due pair whose parent is built, and repeat, until the
# view fits the budget or no pair can merge; c is the next merge. Returns
# the merged parents, in merge order, and the view.
def fit.go(fuel: Nat, c: Maybe<&2, ONode.Node>, +m: Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> List<&2, ONode.Node> & List<&2, ONode.Node>:
  match fuel c:
    case 0n _:
      (Nil{}, v)
    case 1n+f None{}:
      (Nil{}, v)
    case 1n+f Some{+a}:
      +w = merge(info, v, a)
      fit.cons(ONode.Node.parent(a), fit.go(f, choose(m, t, budget, ph, info, w), m, t, budget, ph, info, w))

# fit the view of T messages (t, in binary) into budget bytes, with ph
# bytes for an unbuilt line (each merge drops a line, so the view's length
# bounds the merges)
def fit(+m: Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> List<&2, ONode.Node> & List<&2, ONode.Node>:
  fit.go(List.length(&2, ONode.Node, v), choose(m, t, budget, ph, info, v), m, t, budget, ph, info, v)

def fit.view(+m: Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: OInfo.Info, +v: List<&2, ONode.Node>) -> List<&2, ONode.Node>:
  Pair.snd(List<&2, ONode.Node>, List<&2, ONode.Node>, fit(m, t, budget, ph, info, v))
