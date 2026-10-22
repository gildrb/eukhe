# optchat: the pure core of eukhe's chat memory, after Victor Taelin's
# OptChat gist (docs/memory.md maps every rule of it to this file, to the
# Rust code and to LAWS.bend).
#
# - A node(l, i) covers the 2^l messages from i·2^l on (gist §2). Its
#   index i is kept in binary, lowest bit first, so its parent is one
#   step away: node(l+1, i/2) drops the lowest bit.
# - The view is an ordered list of nodes (gist §3). Each message appends
#   its line; once the view passes the ceiling, one batch merges the most
#   due pairs, due = (T - last) / 2^l, oldest first on ties, until it is
#   at most the floor (gist §3.2).
# - The compaction view is the view merged further, with its own
#   sawtooth; a compaction sees it up to its node (gist §4).
# - The work queue starts nodes in the gist's order (gist §4).
#
# LAWS.bend states what must hold; PROOF.bend proves it. bend/bridge.bend
# runs this model on the scenarios the Rust bridge test sends.

import Base

# Numbers
# -------

# 2^l
def pow2(l: Nat) -> Nat:
  match l:
    case 0n:
      1n
    case 1n+p:
      Nat.double(pow2(p))

# x·2^l
def shl(l: Nat, x: Nat) -> Nat:
  match l:
    case 0n:
      x
    case 1n+p:
      shl(p, Nat.double(x))

# Bits
# ----
# A number in binary, lowest bit first, without high zero bits: 0 is [],
# 6 is [False, True, True].

def bit(b: Bool, x: Nat) -> Nat:
  match b:
    case False{}:
      x
    case True{}:
      1n+x

def Bits.val(bs: List<&2, Bool>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case h <> t:
      bit(h, Nat.double(Bits.val(t)))

def Bits.inc(bs: List<&2, Bool>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      [True{}]
    case h <> t:
      match h:
        case False{}:
          True{} <> t
        case True{}:
          False{} <> Bits.inc(t)

# the lowest bit (0 for 0)
def Bits.low(bs: List<&2, Bool>) -> Bool:
  match bs:
    case Nil{}:
      False{}
    case h <> t:
      h

# the number halved (the bits above the lowest)
def Bits.up(bs: List<&2, Bool>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      Nil{}
    case h <> t:
      t

def Bool.eq(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      Bool.not(b)
    case True{}:
      b

def Bits.eq(as: List<&2, Bool>, bs: List<&2, Bool>) -> Bool:
  match as bs:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> ys:
      False{}
    case x <> xs Nil{}:
      False{}
    case x <> xs y <> ys:
      Bool.and(Bool.eq(x, y), Bits.eq(xs, ys))

# The planner's arithmetic runs on bits, so the kernel checks long runs
# fast; high zero bits are tolerated.

# x·2^l: l zero bits below x
def Bits.shl(l: Nat, x: List<&2, Bool>) -> List<&2, Bool>:
  match l:
    case 0n:
      x
    case 1n+p:
      False{} <> Bits.shl(p, x)

# x + 1 when c holds
def Bits.inc_if(c: Bool, x: List<&2, Bool>) -> List<&2, Bool>:
  match c:
    case False{}:
      x
    case True{}:
      Bits.inc(x)

# x + y + c
def Bits.add.go(xs: List<&2, Bool>, ys: List<&2, Bool>, +c: Bool) -> List<&2, Bool>:
  match xs ys:
    case Nil{} _:
      Bits.inc_if(c, ys)
    case x <> xt Nil{}:
      Bits.inc_if(c, x <> xt)
    case +x <> xt +y <> yt:
      Bool.xor(Bool.xor(x, y), c) <> Bits.add.go(xt, yt, Bool.or(Bool.and(x, y), Bool.and(c, Bool.or(x, y))))

def Bits.add(xs: List<&2, Bool>, ys: List<&2, Bool>) -> List<&2, Bool>:
  Bits.add.go(xs, ys, False{})

def Bits.is_zero(xs: List<&2, Bool>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case h <> t:
      Bool.and(Bool.not(h), Bits.is_zero(t))

# the higher bits decide, unless equal
def Cmp.then(hi: Cmp, lo: Cmp) -> Cmp:
  match hi:
    case EQ{}:
      lo
    case LT{}:
      LT{}
    case GT{}:
      GT{}

def Cmp.of_zero(z: Bool, ne: Cmp) -> Cmp:
  match z:
    case True{}:
      EQ{}
    case False{}:
      ne

def Bits.cmp(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Cmp:
  match xs ys:
    case Nil{} _:
      Cmp.of_zero(Bits.is_zero(ys), LT{})
    case x <> xt Nil{}:
      Cmp.of_zero(Bits.is_zero(x <> xt), GT{})
    case x <> xt y <> yt:
      Cmp.then(Bits.cmp(xt, yt), Bool.cmp(x, y))

def Bits.gt(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Bool:
  Cmp.is_gt(Bits.cmp(xs, ys))

def Bits.le(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Bool:
  Cmp.is_le(Bits.cmp(xs, ys))

def Bits.same(xs: List<&2, Bool>, ys: List<&2, Bool>) -> Bool:
  Cmp.is_eq(Bits.cmp(xs, ys))

# Nodes
# -----

# node(l, i): the 2^l messages from i·2^l on, named id+n with id = i·2^l
# and n = 2^l (gist §2)
type Node is Data:
  Node{l: Nat, i: List<&2, Bool>}

def Node.lvl(n: Node) -> Nat:
  match n:
    case Node{l, i}:
      l

# id: the first message
def Node.start(n: Node) -> Nat:
  match n:
    case Node{l, i}:
      shl(l, Bits.val(i))

# n: how many messages
def Node.count(n: Node) -> Nat:
  match n:
    case Node{l, i}:
      pow2(l)

# one past the last message
def Node.end(+n: Node) -> Nat:
  Nat.add(Node.start(n), Node.count(n))

# the node of message t
def Node.leaf(t: List<&2, Bool>) -> Node:
  Node{0n, t}

# node(l+1, i/2)
def Node.parent(n: Node) -> Node:
  match n:
    case Node{l, i}:
      Node{1n+l, Bits.up(i)}

# a and b are the two halves of one parent, a first
def Node.sib(a: Node, b: Node) -> Bool:
  match a b:
    case Node{la, ia} Node{lb, ib}:
      +ja = ia
      +jb = ib
      Bool.and(Nat.is_eq(la, lb), Bool.and(Bool.not(Bits.low(ja)), Bool.and(Bits.low(jb), Bits.eq(Bits.up(ja), Bits.up(jb)))))

def Node.eq(a: Node, b: Node) -> Bool:
  match a b:
    case Node{la, ia} Node{lb, ib}:
      Bool.and(Nat.is_eq(la, lb), Bits.same(ia, ib))

def Bool.implies(a: Bool, b: Bool) -> Bool:
  match a:
    case False{}:
      True{}
    case True{}:
      b

def Nat.is_pos(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+p:
      True{}

# Built nodes
# -----------
# The size of every built node: one trie per level, keyed by the bits of
# the node's index. All{s} has every node built, each s bytes (for the
# comparison with push, where a line counts 1).

type Trie is Data:
  Tip{}
  Bin{val: Maybe<&2, Nat>, lo: Trie, hi: Trie}

def Trie.get(k: List<&2, Bool>, t: Trie) -> Maybe<&2, Nat>:
  match k t:
    case _ Tip{}:
      None{}
    case Nil{} Bin{v, lo, hi}:
      v
    case False{} <> r Bin{v, lo, hi}:
      Trie.get(r, lo)
    case True{} <> r Bin{v, lo, hi}:
      Trie.get(r, hi)

def Trie.set(k: List<&2, Bool>, t: Trie, +s: Nat) -> Trie:
  match k t:
    case Nil{} Tip{}:
      Bin{Some{s}, Tip{}, Tip{}}
    case Nil{} Bin{v, lo, hi}:
      Bin{Some{s}, lo, hi}
    case False{} <> r Tip{}:
      Bin{None{}, Trie.set(r, Tip{}, s), Tip{}}
    case True{} <> r Tip{}:
      Bin{None{}, Tip{}, Trie.set(r, Tip{}, s)}
    case False{} <> r Bin{v, lo, hi}:
      Bin{v, Trie.set(r, lo, s), hi}
    case True{} <> r Bin{v, lo, hi}:
      Bin{v, lo, Trie.set(r, hi, s)}

type Info is Data:
  All{size: Nat}
  Lvls{ts: List<&2, Trie>}

def Lvls.get(l: Nat, ts: List<&2, Trie>, k: List<&2, Bool>) -> Maybe<&2, Nat>:
  match l ts:
    case _ Nil{}:
      None{}
    case 0n h <> t:
      Trie.get(k, h)
    case 1n+p h <> t:
      Lvls.get(p, t, k)

def Lvls.set(l: Nat, ts: List<&2, Trie>, k: List<&2, Bool>, +s: Nat) -> List<&2, Trie>:
  match l ts:
    case 0n Nil{}:
      [Trie.set(k, Tip{}, s)]
    case 0n h <> t:
      Trie.set(k, h, s) <> t
    case 1n+p Nil{}:
      Tip{} <> Lvls.set(p, Nil{}, k, s)
    case 1n+p h <> t:
      h <> Lvls.set(p, t, k, s)

def Info.empty() -> Info:
  Lvls{Nil{}}

# the node's size, when it is built
def Info.get(info: Info, n: Node) -> Maybe<&2, Nat>:
  match info:
    case All{s}:
      Some{s}
    case Lvls{ts}:
      match n:
        case Node{l, i}:
          Lvls.get(l, ts, i)

# node n is built, s bytes
def Info.set(info: Info, n: Node, +s: Nat) -> Info:
  match info:
    case All{a}:
      All{a}
    case Lvls{ts}:
      match n:
        case Node{l, i}:
          Lvls{Lvls.set(l, ts, i, s)}

def Info.built(info: Info, n: Node) -> Bool:
  Maybe.is_some(&2, Nat, Info.get(info, n))

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

def line_size(+ph: Nat, +info: Info, +n: Node) -> Nat:
  size.of(ph, Info.get(info, n))

def view_size(+ph: Nat, +info: Info, v: List<&2, Node>) -> Nat:
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
def pair_end(+a: Node) -> List<&2, Bool>:
  match a:
    case Node{l, i}:
      Bits.shl(l, Bits.inc(Bits.inc(i)))

def pair_start(+a: Node) -> List<&2, Bool>:
  match a:
    case Node{l, i}:
      Bits.shl(l, i)

# the pair from a on is more due than the pair from b on:
#   Last:  (T - last_a) / 2^la  >  (T - last_b) / 2^lb
#   First: (T - first_a) / 2^la >  (T - first_b) / 2^lb
# Both sides times 2^(la+lb), and T - last = T+1 - e, moved across:
#   Last:  (T+1)·2^lb + e_b·2^la  >  (T+1)·2^la + e_a·2^lb
#   First:     T·2^lb + s_b·2^la  >      T·2^la + s_a·2^lb
def more_due.cross(+u: List<&2, Bool>, +la: Nat, +lb: Nat, xa: List<&2, Bool>, xb: List<&2, Bool>) -> Bool:
  Bits.gt(Bits.add(Bits.shl(lb, u), Bits.shl(la, xb)), Bits.add(Bits.shl(la, u), Bits.shl(lb, xa)))

def more_due(m: Age, +t: List<&2, Bool>, +a: Node, +b: Node) -> Bool:
  match m:
    case Last{}:
      more_due.cross(Bits.inc(t), Node.lvl(a), Node.lvl(b), pair_end(a), pair_end(b))
    case First{}:
      more_due.cross(t, Node.lvl(a), Node.lvl(b), pair_start(a), pair_start(b))

# a and b may merge: they are the halves of a built parent
def mergeable(+info: Info, +a: Node, +b: Node) -> Bool:
  Bool.and(Node.sib(a, b), Info.built(info, Node.parent(a)))

# a and the next line (if any) may merge
def pair.ok(+info: Info, +a: Node, next: Maybe<&2, Node>) -> Bool:
  match next:
    case None{}:
      False{}
    case Some{b}:
      mergeable(info, a, b)

def best.vs(more: Bool, +a: Node, c: Node) -> Node:
  match more:
    case True{}:
      a
    case False{}:
      c

def best.take(+m: Age, +t: List<&2, Bool>, +a: Node, cur: Maybe<&2, Node>) -> Maybe<&2, Node>:
  match cur:
    case None{}:
      Some{a}
    case Some{+c}:
      Some{best.vs(more_due(m, t, a, c), a, c)}

def best.pick(ok: Bool, +m: Age, +t: List<&2, Bool>, +a: Node, cur: Maybe<&2, Node>) -> Maybe<&2, Node>:
  match ok:
    case False{}:
      cur
    case True{}:
      best.take(m, t, a, cur)

def best.pair(+m: Age, +t: List<&2, Bool>, +info: Info, +a: Node, next: Maybe<&2, Node>, cur: Maybe<&2, Node>) -> Maybe<&2, Node>:
  match next:
    case None{}:
      cur
    case Some{b}:
      best.pick(mergeable(info, a, b), m, t, a, cur)

# scan the pairs oldest first; a later pair wins only when strictly more
# due, so of equal pairs the oldest stays. cur is the first line of the
# most due pair so far.
def best.go(+m: Age, +t: List<&2, Bool>, +info: Info, v: List<&2, Node>, cur: Maybe<&2, Node>) -> Maybe<&2, Node>:
  match v:
    case Nil{}:
      cur
    case +a <> +rest:
      best.go(m, t, info, rest, best.pair(m, t, info, a, List.head(&2, Node, rest), cur))

# the first line of the most due mergeable pair, if any; t is T, the
# number of messages, in binary
def best(+m: Age, +t: List<&2, Bool>, +info: Info, v: List<&2, Node>) -> Maybe<&2, Node>:
  best.go(m, t, info, v, None{})

# Merging
# -------

def merge.pick(hit: Bool, +x: Node, +y: Node, more: List<&2, Node>, rec: List<&2, Node>) -> List<&2, Node>:
  match hit:
    case True{}:
      Node.parent(x) <> more
    case False{}:
      x <> rec

def merge.here(+info: Info, +a: Node, +x: Node, rest: List<&2, Node>, rec: List<&2, Node>) -> List<&2, Node>:
  match rest:
    case Nil{}:
      [x]
    case +y <> more:
      merge.pick(Bool.and(Node.eq(x, a), mergeable(info, x, y)), x, y, more, rec)

# the first pair (a, y) of v that may merge, replaced by its parent
def merge(+info: Info, v: List<&2, Node>, +a: Node) -> List<&2, Node>:
  match v:
    case Nil{}:
      Nil{}
    case +x <> +rest:
      merge.here(info, a, x, rest, merge(info, rest, a))

def choose.if(over: Bool, +m: Age, +t: List<&2, Bool>, +info: Info, v: List<&2, Node>) -> Maybe<&2, Node>:
  match over:
    case False{}:
      None{}
    case True{}:
      best(m, t, info, v)

# the next merge of a fit: the most due pair, while over budget
def choose(+m: Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: Info, +v: List<&2, Node>) -> Maybe<&2, Node>:
  choose.if(Nat.is_gt(view_size(ph, info, v), budget), m, t, info, v)

def fit.cons(n: Node, r: List<&2, Node> & List<&2, Node>) -> List<&2, Node> & List<&2, Node>:
  (ms, out) = r
  (n <> ms, out)

# merge the most due pair whose parent is built, and repeat, until the
# view fits the budget or no pair can merge; c is the next merge. Returns
# the merged parents, in merge order, and the view.
def fit.go(fuel: Nat, c: Maybe<&2, Node>, +m: Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: Info, +v: List<&2, Node>) -> List<&2, Node> & List<&2, Node>:
  match fuel c:
    case 0n _:
      (Nil{}, v)
    case 1n+f None{}:
      (Nil{}, v)
    case 1n+f Some{+a}:
      +w = merge(info, v, a)
      fit.cons(Node.parent(a), fit.go(f, choose(m, t, budget, ph, info, w), m, t, budget, ph, info, w))

# fit the view of T messages (t, in binary) into budget bytes, with ph
# bytes for an unbuilt line (each merge drops a line, so the view's length
# bounds the merges)
def fit(+m: Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: Info, +v: List<&2, Node>) -> List<&2, Node> & List<&2, Node>:
  fit.go(List.length(&2, Node, v), choose(m, t, budget, ph, info, v), m, t, budget, ph, info, v)

def fit.view(+m: Age, +t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: Info, +v: List<&2, Node>) -> List<&2, Node>:
  Pair.snd(List<&2, Node>, List<&2, Node>, fit(m, t, budget, ph, info, v))

# Taelin's rollback push
# ----------------------
# rollback_state_list.js (2022), verbatim; the list is newest first, and a
# state is a message id, in binary.

type Entry is Data:
  Entry{keep: Nat, life: Nat, state: List<&2, Bool>}

def push(states: List<&2, Entry>, +s: List<&2, Bool>) -> List<&2, Entry>:
  match states:
    case Nil{}:
      [Entry{0n, 0n, s}]
    case e <> older:
      match e:
        case Entry{keep, life, state}:
          match keep:
            case 0n:
              Entry{1n, life, state} <> older
            case 1n+kp:
              match life:
                case 1n+lp:
                  Entry{0n, 0n, s} <> Entry{0n, lp, state} <> older
                case 0n:
                  Entry{0n, 0n, s} <> push(older, state)

def Bitss.same(as: List<&2, List<&2, Bool>>, bs: List<&2, List<&2, Bool>>) -> Bool:
  match as bs:
    case Nil{} Nil{}:
      True{}
    case Nil{} y <> ys:
      False{}
    case x <> xs Nil{}:
      False{}
    case x <> xs y <> ys:
      Bool.and(Bits.same(x, y), Bitss.same(xs, ys))

def starts(v: List<&2, Node>) -> List<&2, List<&2, Bool>>:
  match v:
    case Nil{}:
      Nil{}
    case h <> t:
      pair_start(h) <> starts(t)

def states(es: List<&2, Entry>) -> List<&2, List<&2, Bool>>:
  match es:
    case Nil{}:
      Nil{}
    case e <> t:
      match e:
        case Entry{k, l, s}:
          s <> states(t)

# the view is push's list, oldest first: each state starts a line
def same_lines(+v: List<&2, Node>, +es: List<&2, Entry>) -> Bool:
  Bitss.same(starts(v), List.reverse(&2, List<&2, Bool>, states(es)))

# Push t = 0..n-1, one message each; the view appends each message and
# fits push's list length (every line 1 byte, every node built). True when
# the two agree after every push.
def agree.go(n: Nat, +m: Age, +tb: List<&2, Bool>, +es: List<&2, Entry>, +v: List<&2, Node>) -> Bool:
  match n:
    case 0n:
      True{}
    case 1n+p:
      +es2 = push(es, tb)
      +tb2 = Bits.inc(tb)
      +v2 = fit.view(m, tb2, List.length(&2, Entry, es2), 0n, All{1n}, List.append(&2, Node, v, [Node.leaf(tb)]))
      Bool.and(same_lines(v2, es2), agree.go(p, m, tb2, es2, v2))

def agree(+m: Age, n: Nat) -> Bool:
  agree.go(n, m, Nil{}, Nil{}, Nil{})

# how many of the pushes t = 0..n-1 the view agrees with
def agree.count.go(n: Nat, +m: Age, +tb: List<&2, Bool>, +es: List<&2, Entry>, +v: List<&2, Node>) -> Nat:
  match n:
    case 0n:
      0n
    case 1n+p:
      +es2 = push(es, tb)
      +tb2 = Bits.inc(tb)
      +v2 = fit.view(m, tb2, List.length(&2, Entry, es2), 0n, All{1n}, List.append(&2, Node, v, [Node.leaf(tb)]))
      Nat.add(bit(same_lines(v2, es2), 0n), agree.count.go(p, m, tb2, es2, v2))

def agree.count(+m: Age, n: Nat) -> Nat:
  agree.count.go(n, m, Nil{}, Nil{}, Nil{})

# The chat
# --------
# The sizes: ph bytes for a line not summarized yet; the view's sawtooth
# from ceil down to floor (gist §3.2); the compaction view's from cceil
# down to cfloor (gist §4); jobs calls at once (gist §4).

type Cfg is Data:
  Cfg{ph: Nat, ceil: Nat, floor: Nat, cceil: Nat, cfloor: Nat, jobs: Nat}

def Cfg.ph(c: Cfg) -> Nat:
  match c:
    case Cfg{ph, ce, fl, cc, cf, j}:
      ph

def Cfg.ceil(c: Cfg) -> Nat:
  match c:
    case Cfg{ph, ce, fl, cc, cf, j}:
      ce

def Cfg.floor(c: Cfg) -> Nat:
  match c:
    case Cfg{ph, ce, fl, cc, cf, j}:
      fl

def Cfg.cceil(c: Cfg) -> Nat:
  match c:
    case Cfg{ph, ce, fl, cc, cf, j}:
      cc

def Cfg.cfloor(c: Cfg) -> Nat:
  match c:
    case Cfg{ph, ce, fl, cc, cf, j}:
      cf

def Cfg.jobs(c: Cfg) -> Nat:
  match c:
    case Cfg{ph, ce, fl, cc, cf, j}:
      j

# the gist's sizes; the placeholder is "(not summarized yet: zoom it)"
def Cfg.gist() -> Cfg:
  Cfg{29n, 128000n, 64000n, 32000n, 16000n, 8n}

# T (in binary), the built nodes, the view, whether a batch is still
# shrinking it, the compaction view, the ready merges (by level, then
# index) and the nodes being built
type St is Data:
  St{t: List<&2, Bool>, info: Info, view: List<&2, Node>, shrink: Bool, cview: List<&2, Node>, ready: List<&2, Node>, busy: List<&2, Node>}

def St.empty() -> St:
  St{Nil{}, Info.empty(), Nil{}, False{}, Nil{}, Nil{}, Nil{}}

def St.t(s: St) -> List<&2, Bool>:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      t

def St.info(s: St) -> Info:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      info

def St.view(s: St) -> List<&2, Node>:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      view

def St.shrink(s: St) -> Bool:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      shrink

def St.cview(s: St) -> List<&2, Node>:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      cview

def St.ready(s: St) -> List<&2, Node>:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      ready

def St.busy(s: St) -> List<&2, Node>:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      busy

# What happens to the chat: a message is logged; a node is built (s
# bytes); a node's call starts; a call fails (its node may start again).
type Ev is Data:
  Msg{}
  Build{n: Node, size: Nat}
  Start{n: Node}
  Free{n: Node}

# a before b: by level, then index
def Node.lt(a: Node, b: Node) -> Bool:
  match a b:
    case Node{+la, ia} Node{+lb, ib}:
      Bool.or(Nat.is_lt(la, lb), Bool.and(Nat.is_eq(la, lb), Cmp.is_lt(Bits.cmp(ia, ib))))

def Nodes.has(xs: List<&2, Node>, +x: Node) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case h <> t:
      Bool.or(Node.eq(h, x), Nodes.has(t, x))

def Nodes.keep(k: Bool, +h: Node, t: List<&2, Node>) -> List<&2, Node>:
  match k:
    case False{}:
      t
    case True{}:
      h <> t

def Nodes.del(xs: List<&2, Node>, +x: Node) -> List<&2, Node>:
  match xs:
    case Nil{}:
      Nil{}
    case +h <> t:
      Nodes.keep(Bool.not(Node.eq(h, x)), h, Nodes.del(t, x))

def Nodes.ins.at(here: Bool, same: Bool, +x: Node, +h: Node, t: List<&2, Node>, rec: List<&2, Node>) -> List<&2, Node>:
  match here same:
    case True{} _:
      x <> h <> t
    case False{} True{}:
      h <> t
    case False{} False{}:
      h <> rec

# x into the sorted xs, once
def Nodes.ins(xs: List<&2, Node>, +x: Node) -> List<&2, Node>:
  match xs:
    case Nil{}:
      [x]
    case +h <> +t:
      Nodes.ins.at(Node.lt(x, h), Node.eq(x, h), x, h, t, Nodes.ins(t, x))

def Nodes.add(xs: List<&2, Node>, +x: Node) -> List<&2, Node>:
  +ys = xs
  Nodes.keep(Bool.not(Nodes.has(ys, x)), x, ys)

# the other half of n's parent
def Bits.flip(bs: List<&2, Bool>) -> List<&2, Bool>:
  match bs:
    case Nil{}:
      [True{}]
    case False{} <> t:
      True{} <> t
    case True{} <> t:
      match t:
        case Nil{}:
          Nil{}
        case h <> r:
          False{} <> h <> r

def Node.sibling(n: Node) -> Node:
  match n:
    case Node{l, i}:
      Node{l, Bits.flip(i)}

# The compaction view: past cceil, it merges down to cfloor
def fitc.if(over: Bool, +cfg: Cfg, +t: List<&2, Bool>, +info: Info, +cv: List<&2, Node>) -> List<&2, Node>:
  match over:
    case False{}:
      cv
    case True{}:
      fit.view(Last{}, t, Cfg.cfloor(cfg), Cfg.ph(cfg), info, cv)

def fitc(+cfg: Cfg, +t: List<&2, Bool>, +info: Info, +cv: List<&2, Node>) -> List<&2, Node>:
  fitc.if(Nat.is_gt(view_size(Cfg.ph(cfg), info, cv), Cfg.cceil(cfg)), cfg, t, info, cv)

# A message
# ---------
# Its line is appended to both views. Once the view passes ceil, a batch
# merges it down to floor; while unbuilt parents keep it above floor, each
# new message merges what it can. When the view merges, the compaction
# view starts again from it, merged down to cfloor; else it keeps its own
# sawtooth.

def msg.cview(merged: List<&2, Node>, +cfg: Cfg, +t: List<&2, Bool>, +info: Info, +view: List<&2, Node>, +cv: List<&2, Node>) -> List<&2, Node>:
  match merged:
    case Nil{}:
      fitc(cfg, t, info, cv)
    case h <> rest:
      fit.view(Last{}, t, Cfg.cfloor(cfg), Cfg.ph(cfg), info, view)

def msg.after(+merged: List<&2, Node>, +view: List<&2, Node>, +cfg: Cfg, +t: List<&2, Bool>, +info: Info, +cv: List<&2, Node>, ready: List<&2, Node>, busy: List<&2, Node>) -> St & List<&2, Node>:
  (St{t, info, view, Nat.is_gt(view_size(Cfg.ph(cfg), info, view), Cfg.floor(cfg)), msg.cview(merged, cfg, t, info, view, cv), ready, busy}, merged)

def msg.batch(r: List<&2, Node> & List<&2, Node>, +cfg: Cfg, +t: List<&2, Bool>, +info: Info, +cv: List<&2, Node>, ready: List<&2, Node>, busy: List<&2, Node>) -> St & List<&2, Node>:
  (merged, view) = r
  msg.after(merged, view, cfg, t, info, cv, ready, busy)

def msg.go(grow: Bool, +cfg: Cfg, +t: List<&2, Bool>, +info: Info, +view: List<&2, Node>, +cv: List<&2, Node>, ready: List<&2, Node>, busy: List<&2, Node>) -> St & List<&2, Node>:
  match grow:
    case False{}:
      (St{t, info, view, False{}, fitc(cfg, t, info, cv), ready, busy}, Nil{})
    case True{}:
      msg.batch(fit(Last{}, t, Cfg.floor(cfg), Cfg.ph(cfg), info, view), cfg, t, info, cv, ready, busy)

# the view with message t's line
def St.grown(+s: St) -> List<&2, Node>:
  List.append(&2, Node, St.view(s), [Node.leaf(St.t(s))])

# a batch runs (or goes on) at this message
def St.batch(+cfg: Cfg, +s: St) -> Bool:
  Bool.or(St.shrink(s), Nat.is_gt(view_size(Cfg.ph(cfg), St.info(s), St.grown(s)), Cfg.ceil(cfg)))

# message T arrives: the state after it, and the batch it set off (the
# merged parents, in order; empty when none)
def msg(+cfg: Cfg, +s: St) -> St & List<&2, Node>:
  msg.go(St.batch(cfg, s), cfg, Bits.inc(St.t(s)), St.info(s), St.grown(s), List.append(&2, Node, St.cview(s), [Node.leaf(St.t(s))]), St.ready(s), St.busy(s))

# A built node
# ------------
# It is logged; its parent becomes ready once its sibling is built too
# (a queue, never a scan of the tree: gist §4); the compaction view keeps
# its sawtooth. The view never merges here: only a message merges it.

def ready.if(go: Bool, +p: Node, rs: List<&2, Node>) -> List<&2, Node>:
  match go:
    case False{}:
      rs
    case True{}:
      Nodes.ins(rs, p)

def ready.note(+info: Info, +n: Node, rs: List<&2, Node>) -> List<&2, Node>:
  ready.if(Bool.and(Info.built(info, Node.sibling(n)), Bool.not(Info.built(info, Node.parent(n)))), Node.parent(n), rs)

def build.go(+cfg: Cfg, +n: Node, +info: Info, s: St) -> St:
  match s:
    case St{+t, i0, view, shrink, cview, ready, busy}:
      St{t, info, view, shrink, fitc(cfg, t, info, cview), ready.note(info, n, Nodes.del(ready, n)), Nodes.del(busy, n)}

def build(+cfg: Cfg, +s: St, +n: Node, +size: Nat) -> St:
  build.go(cfg, n, Info.set(St.info(s), n, size), s)

def busy.set(s: St, bs: List<&2, Node>) -> St:
  match s:
    case St{t, info, view, shrink, cview, ready, busy}:
      St{t, info, view, shrink, cview, ready, bs}

# one event: the state after it, and the batch it set off
def step(+cfg: Cfg, +s: St, e: Ev) -> St & List<&2, Node>:
  match e:
    case Msg{}:
      msg(cfg, s)
    case Build{n, size}:
      (build(cfg, s, n, size), Nil{})
    case Start{n}:
      (busy.set(s, Nodes.add(St.busy(s), n)), Nil{})
    case Free{n}:
      (busy.set(s, Nodes.del(St.busy(s), n)), Nil{})

def run.go(evs: List<&2, Ev>, +cfg: Cfg, +s: St) -> St:
  match evs:
    case Nil{}:
      s
    case e <> rest:
      run.go(rest, cfg, Pair.fst(St, List<&2, Node>, step(cfg, s, e)))

# the chat after evs, from an empty one
def run(+cfg: Cfg, evs: List<&2, Ev>) -> St:
  run.go(evs, cfg, St.empty())

# The work queue
# --------------
# A message's node starts once fewer than jobs lines before it are still
# unbuilt; a merge starts once both its halves are built (it is ready).
# At most jobs calls run at once (gist §4).

def cand.emit(stop: Bool, built: Bool, free: Bool, +h: Node, rec: List<&2, Node>) -> List<&2, Node>:
  match stop built free:
    case True{} _ _:
      Nil{}
    case False{} True{} _:
      rec
    case False{} False{} True{}:
      h <> rec
    case False{} False{} False{}:
      rec

# the view's unbuilt lines that may start: unb unbuilt lines seen, room
# free slots left
def cand.view(v: List<&2, Node>, +info: Info, +busy: List<&2, Node>, +jobs: Nat, +unb: Nat, room: Nat) -> List<&2, Node>:
  match v room:
    case Nil{} _:
      Nil{}
    case h <> rest 0n:
      Nil{}
    case +h <> rest 1n+r:
      +built = Info.built(info, h)
      +free = Bool.not(Nodes.has(busy, h))
      cand.emit(Nat.is_ge(unb, jobs), built, free, h, cand.view(rest, info, busy, jobs, Nat.add(unb, bit(Bool.not(built), 0n)), Nat.sub(1n+r, bit(Bool.and(Bool.not(built), free), 0n))))

def cand.ready(rs: List<&2, Node>, +busy: List<&2, Node>, room: Nat) -> List<&2, Node>:
  match rs room:
    case Nil{} _:
      Nil{}
    case h <> rest 0n:
      Nil{}
    case +h <> rest 1n+r:
      +free = Bool.not(Nodes.has(busy, h))
      Nodes.keep(free, h, cand.ready(rest, busy, Nat.sub(1n+r, bit(free, 0n))))

def cands.with(+s: St, +room: Nat, c0: List<&2, Node>) -> List<&2, Node>:
  +c = c0
  List.append(&2, Node, c, cand.ready(St.ready(s), St.busy(s), Nat.sub(room, List.length(&2, Node, c))))

# the nodes to start now, oldest message first, then the ready merges
def cands(+cfg: Cfg, +s: St) -> List<&2, Node>:
  +room = Nat.sub(Cfg.jobs(cfg), List.length(&2, Node, St.busy(s)))
  cands.with(s, room, cand.view(St.view(s), St.info(s), St.busy(s), Cfg.jobs(cfg), 0n, room))

# the nodes to start while a turn waits for the view: the view's unbuilt
# lines only, oldest first; the ready merges wait (docs/harness.md H2.1)
def cands.need(+cfg: Cfg, +s: St) -> List<&2, Node>:
  cand.view(St.view(s), St.info(s), St.busy(s), Cfg.jobs(cfg), 0n, Nat.sub(Cfg.jobs(cfg), List.length(&2, Node, St.busy(s))))

# the busy nodes that are view lines still unbuilt
def busy.need(+info: Info, +v: List<&2, Node>, bs: List<&2, Node>) -> List<&2, Node>:
  match bs:
    case Nil{}:
      Nil{}
    case +b <> rest:
      Nodes.keep(Bool.and(Nodes.has(v, b), Bool.not(Info.built(info, b))), b, busy.need(info, v, rest))

# a turn starts to wait: every call of a node it does not need stops, and
# the node goes back to the queue (docs/harness.md H2.1)
def St.wait(s: St) -> St:
  match s:
    case St{t, +info, +view, shrink, cview, ready, busy}:
      St{t, info, view, shrink, cview, ready, busy.need(info, view, busy)}

# A compaction's view
# -------------------
# The compaction view up to the node: the lines before the message, or
# for a merge the lines up to its last message; it stops at the first
# unbuilt line (gist §4).

def Node.end_bits(n: Node) -> List<&2, Bool>:
  match n:
    case Node{l, i}:
      Bits.shl(l, Bits.inc(i))

def ctx.bound(n: Node) -> List<&2, Bool>:
  match n:
    case Node{l, i}:
      match l:
        case 0n:
          i
        case 1n+p:
          Bits.shl(1n+p, Bits.inc(i))

def ctx.keep(k: Bool, +h: Node, rec: List<&2, Node>) -> List<&2, Node>:
  match k:
    case False{}:
      Nil{}
    case True{}:
      h <> rec

# a line stays when it ends by the bound and is built
def ctx.ok(+info: Info, +bound: List<&2, Bool>, +h: Node) -> Bool:
  Bool.and(Bits.le(Node.end_bits(h), bound), Info.built(info, h))

def ctx.go(v: List<&2, Node>, +info: Info, +bound: List<&2, Bool>) -> List<&2, Node>:
  match v:
    case Nil{}:
      Nil{}
    case +h <> rest:
      ctx.keep(ctx.ok(info, bound, h), h, ctx.go(rest, info, bound))

# the view a compaction of node n sees
def ctx(+s: St, +n: Node) -> List<&2, Node>:
  ctx.go(St.cview(s), St.info(s), ctx.bound(n))

# The shipped batch
# -----------------
# fit with the Last measure, fast: on a view that tiles the messages it is
# fit itself (law fitx_is_fit). A merge always makes its parent's pair less
# due than the pair it merged, so no pair can become mergeable after a less
# due one: the batch takes, in one sort, every pair that could ever merge
# (each line's built ancestors), most due first (of equal ones the older),
# and merges each in turn whose two halves are lines then, while the view
# is over budget. O(L log L) instead of O(L) per merge.
#
# A map from nodes to sizes: per level (lowest first), a trie on the index
# bits. Used linearly (never shared).
type Mt is Data:
  MtTip{}
  MtBin{v: Maybe<&2, Nat>, lo: Mt, hi: Mt}

type Sizes is Data:
  SzEnd{}
  SzLv{t: Mt, rest: Sizes}

def mt.get(k: List<&2, Bool>, t: Mt) -> Maybe<&2, Nat>:
  match k t:
    case _ MtTip{}:
      None{}
    case Nil{} MtBin{v, lo, hi}:
      v
    case False{} <> r MtBin{v, lo, hi}:
      mt.get(r, lo)
    case True{} <> r MtBin{v, lo, hi}:
      mt.get(r, hi)

def mt.put(k: List<&2, Bool>, t: Mt, +z: Nat) -> Mt:
  match k t:
    case Nil{} MtTip{}:
      MtBin{Some{z}, MtTip{}, MtTip{}}
    case Nil{} MtBin{v, lo, hi}:
      MtBin{Some{z}, lo, hi}
    case False{} <> r MtTip{}:
      MtBin{None{}, mt.put(r, MtTip{}, z), MtTip{}}
    case True{} <> r MtTip{}:
      MtBin{None{}, MtTip{}, mt.put(r, MtTip{}, z)}
    case False{} <> r MtBin{v, lo, hi}:
      MtBin{v, mt.put(r, lo, z), hi}
    case True{} <> r MtBin{v, lo, hi}:
      MtBin{v, lo, mt.put(r, hi, z)}

def sizes.get(l: Nat, k: List<&2, Bool>, s: Sizes) -> Maybe<&2, Nat>:
  match l s:
    case _ SzEnd{}:
      None{}
    case 0n SzLv{t, rest}:
      mt.get(k, t)
    case 1n+p SzLv{t, rest}:
      sizes.get(p, k, rest)

def sizes.put(l: Nat, k: List<&2, Bool>, s: Sizes, +z: Nat) -> Sizes:
  match l s:
    case 0n SzEnd{}:
      SzLv{mt.put(k, MtTip{}, z), SzEnd{}}
    case 0n SzLv{t, rest}:
      SzLv{mt.put(k, t, z), rest}
    case 1n+p SzEnd{}:
      SzLv{MtTip{}, sizes.put(p, k, SzEnd{}, z)}
    case 1n+p SzLv{t, rest}:
      SzLv{t, sizes.put(p, k, rest, z)}

def fitx.get(+s: Sizes, n: Node) -> Maybe<&2, Nat>:
  match n:
    case Node{l, i}:
      sizes.get(l, i, s)

def fitx.put(s: Sizes, n: Node, +z: Nat) -> Sizes:
  match n:
    case Node{l, i}:
      sizes.put(l, i, s, z)

def fitx.has(+s: Sizes, n: Node) -> Bool:
  Maybe.is_some(&2, Nat, fitx.get(s, n))

# 2i in bits, without a high zero bit
def fitx.dbl(i: List<&2, Bool>) -> List<&2, Bool>:
  match i:
    case Nil{}:
      Nil{}
    case h <> t:
      False{} <> h <> t

# the first line of the pair whose parent is p
def fitx.head(p: Node) -> Node:
  match p:
    case Node{l, i}:
      match l:
        case 0n:
          Node{0n, fitx.dbl(i)}
        case 1n+k:
          Node{k, fitx.dbl(i)}

# the pair's second line (h has low bit 0)
def fitx.second(h: Node) -> Node:
  match h:
    case Node{l, i}:
      Node{l, Bits.inc(i)}

# The lines: their sizes (a map) and the view's size, in one pass.
def fitx.lines(v: List<&2, Node>, +ph: Nat, +info: Info, s: Sizes, z: Nat) -> Sizes & Nat:
  match v:
    case Nil{}:
      (s, z)
    case +x <> rest:
      +sz = line_size(ph, info, x)
      fitx.lines(rest, ph, info, fitx.put(s, x, sz), Nat.add(z, sz))

# A pair that may merge: its first line and its parent's size.
type Cand is Data:
  Cand{h: Node, z: Nat}

# from p up: every built ancestor not seen yet
def fitx.up(fuel: Nat, got: Maybe<&2, Nat>, there: Bool, +info: Info, +p: Node, xs: List<&2, Cand>, seen: Sizes) -> List<&2, Cand> & Sizes:
  match fuel got there:
    case 0n _ _:
      (xs, seen)
    case 1n+f None{} _:
      (xs, seen)
    case 1n+f Some{z} True{}:
      (xs, seen)
    case 1n+f Some{+z} False{}:
      +q = Node.parent(p)
      +seen2 = fitx.put(seen, p, z)
      fitx.up(f, Info.get(info, q), fitx.has(seen2, q), info, q, Cand{fitx.head(p), z} <> xs, seen2)

def fitx.all.step(+fuel: Nat, +info: Info, +x: Node, r: List<&2, Cand> & Sizes) -> List<&2, Cand> & Sizes:
  (xs, seen) = r
  +s = seen
  +p = Node.parent(x)
  fitx.up(fuel, Info.get(info, p), fitx.has(s, p), info, p, xs, s)

def fitx.all(v: List<&2, Node>, +fuel: Nat, +info: Info, r: List<&2, Cand> & Sizes) -> List<&2, Cand> & Sizes:
  match v:
    case Nil{}:
      r
    case x <> rest:
      fitx.all(rest, fuel, info, fitx.all.step(fuel, info, x, r))

# Keys. The pair from h = (l, i) is due (u - e)/2^l, with u = T + 1 and
# e = (i+2)·2^l its end: the whole number q = (u >> l) - i - 2 plus the
# fraction (u mod 2^l)/2^l, kept as f = (u mod 2^l)·2^(H - l) for the
# highest level H. Every number here is at most u.

# the value of bits (2x as x + x: native)
def fitx.val(bs: List<&2, Bool>) -> Nat:
  match bs:
    case Nil{}:
      0n
    case h <> t:
      +v = fitx.val(t)
      bit(h, Nat.add(v, v))

# x·2^k
def fitx.shl(k: Nat, x: Nat) -> Nat:
  match k:
    case 0n:
      x
    case 1n+j:
      +y = x
      fitx.shl(j, Nat.add(y, y))

def fitx.take(k: Nat, bs: List<&2, Bool>) -> List<&2, Bool>:
  match k bs:
    case 0n _:
      Nil{}
    case 1n+j Nil{}:
      Nil{}
    case 1n+j h <> t:
      h <> fitx.take(j, t)

def fitx.drop(k: Nat, bs: List<&2, Bool>) -> List<&2, Bool>:
  match k bs:
    case 0n bs:
      bs
    case 1n+j Nil{}:
      Nil{}
    case 1n+j h <> t:
      fitx.drop(j, t)

type Due is Data:
  Due{q: Nat, f: Nat, s: Nat, p: Cand}

def Due.c(x: Due) -> Cand:
  match x:
    case Due{q, f, s, p}:
      p

def fitx.key(+u: List<&2, Bool>, +top: Nat, p: Cand) -> Due:
  match p:
    case Cand{h, z}:
      match h:
        case Node{+l, +i}:
          +iv = fitx.val(i)
          Due{Nat.sub(fitx.val(fitx.drop(l, u)), Nat.add(iv, 2n)), fitx.shl(Nat.sub(top, l), fitx.val(fitx.take(l, u))), fitx.shl(l, iv), Cand{Node{l, i}, z}}

def fitx.keys(ps: List<&2, Cand>, +u: List<&2, Bool>, +top: Nat) -> List<&2, Due>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      fitx.key(u, top, p) <> fitx.keys(rest, u, top)

def fitx.hi(ps: List<&2, Cand>, acc: Nat) -> Nat:
  match ps:
    case Nil{}:
      acc
    case Cand{h, z} <> rest:
      fitx.hi(rest, Nat.max(acc, Node.lvl(h)))

def fitx.tie2(c: Cmp, +sa: Nat, +sb: Nat) -> Bool:
  match c:
    case GT{}:
      True{}
    case LT{}:
      False{}
    case EQ{}:
      Nat.is_lt(sa, sb)

def fitx.tie(c: Cmp, +fa: Nat, +fb: Nat, +sa: Nat, +sb: Nat) -> Bool:
  match c:
    case GT{}:
      True{}
    case LT{}:
      False{}
    case EQ{}:
      fitx.tie2(Nat.cmp(fa, fb), sa, sb)

# a before b: more due, or as due and older
def fitx.before(+a: Due, +b: Due) -> Bool:
  match a b:
    case Due{+qa, +fa, +sa, pa} Due{+qb, +fb, +sb, pb}:
      fitx.tie(Nat.cmp(qa, qb), fa, fb, sa, sb)

# merge sort (the binary counter of the skill's sort example)
type KTree is Data:
  KTip{}
  KLeaf{n: Due}
  KNode{l: KTree, r: KTree}

type KDigits is Data:
  KEnd{}
  KZero{rest: KDigits}
  KOne{tree: KTree, rest: KDigits}

def kd.push(ds: KDigits, t: KTree) -> KDigits:
  match ds:
    case KEnd{}:
      KOne{t, KEnd{}}
    case KZero{rest}:
      KOne{t, rest}
    case KOne{t2, rest}:
      KZero{kd.push(rest, KNode{t2, t})}

def kd.build(xs: List<&2, Due>, ds: KDigits) -> KDigits:
  match xs:
    case Nil{}:
      ds
    case h <> t:
      kd.build(t, kd.push(ds, KLeaf{h}))

def kd.join(ds: KDigits, acc: KTree) -> KTree:
  match ds:
    case KEnd{}:
      acc
    case KZero{rest}:
      kd.join(rest, acc)
    case KOne{t, rest}:
      kd.join(rest, KNode{t, acc})

def kmerge.go(xt: List<&2, Due>, yt: List<&2, Due>, +x: Due, +y: Due, x_first: Bool) -> List<&2, Due>:
  match xt yt x_first:
    case Nil{} Nil{} True{}:
      x <> y <> Nil{}
    case Nil{} Nil{} False{}:
      y <> x <> Nil{}
    case Nil{} +y2 <> yt2 True{}:
      x <> y <> y2 <> yt2
    case Nil{} +y2 <> yt2 False{}:
      y <> kmerge.go(Nil{}, yt2, x, y2, fitx.before(x, y2))
    case +x2 <> xt2 Nil{} True{}:
      x <> kmerge.go(xt2, Nil{}, x2, y, fitx.before(x2, y))
    case +x2 <> xt2 Nil{} False{}:
      y <> x <> x2 <> xt2
    case +x2 <> xt2 +y2 <> yt2 True{}:
      x <> kmerge.go(xt2, y2 <> yt2, x2, y, fitx.before(x2, y))
    case +x2 <> xt2 +y2 <> yt2 False{}:
      y <> kmerge.go(x2 <> xt2, yt2, x, y2, fitx.before(x, y2))

def kmerge(xs: List<&2, Due>, ys: List<&2, Due>) -> List<&2, Due>:
  match xs ys:
    case Nil{} Nil{}:
      Nil{}
    case Nil{} +y <> yt:
      y <> yt
    case +x <> xt Nil{}:
      x <> xt
    case +x <> xt +y <> yt:
      kmerge.go(xt, yt, x, y, fitx.before(x, y))

def ksort(tr: KTree) -> List<&2, Due>:
  match tr:
    case KTip{}:
      Nil{}
    case KLeaf{n}:
      [n]
    case KNode{l, r}:
      kmerge(ksort(l), ksort(r))

def fitx.pairs(ks: List<&2, Due>) -> List<&2, Cand>:
  match ks:
    case Nil{}:
      Nil{}
    case k <> rest:
      Due.c(k) <> fitx.pairs(rest)

def fitx.sort(+t: List<&2, Bool>, +ps: List<&2, Cand>) -> List<&2, Cand>:
  fitx.pairs(ksort(kd.join(kd.build(fitx.keys(ps, Bits.inc(t), fitx.hi(ps, 0n)), KEnd{}), KTip{})))

# The pass: in that order, merge each pair whose two halves are lines now,
# while the view is over budget. lines: the line sizes (merged parents
# included), size: the view's bytes, acc: the merged parents, newest first.
type Pass is Data:
  Pass{lines: Sizes, size: Nat, acc: List<&2, Node>}

def fitx.hit(a: Maybe<&2, Nat>, b: Maybe<&2, Nat>, +h: Node, +z: Nat, s: Pass) -> Pass:
  match a b:
    case Some{x} Some{y}:
      match s:
        case Pass{lines, size, acc}:
          +p = Node.parent(h)
          Pass{fitx.put(lines, p, z), Nat.add(Nat.sub(size, Nat.add(x, y)), z), p <> acc}
    case _ _:
      s

def fitstepx(p: Cand, s: Pass) -> Pass:
  match p s:
    case Cand{+h, +z} Pass{+lines, size, acc}:
      fitx.hit(fitx.get(lines, h), fitx.get(lines, fitx.second(h)), h, z, Pass{lines, size, acc})

def fitx.size(s: Pass) -> Nat:
  match s:
    case Pass{l, z, a}:
      z

def fitx.pass(ps: List<&2, Cand>, over: Bool, +budget: Nat, s: Pass) -> Pass:
  match ps over:
    case Nil{} _:
      s
    case h <> rest False{}:
      s
    case h <> rest True{}:
      +s2 = fitstepx(h, s)
      fitx.pass(rest, Nat.is_gt(fitx.size(s2), budget), budget, s2)

# The view after the merges: a line stays unless merged; a merged parent
# takes the place of its first line.
def fitx.low(x: Node) -> Bool:
  match x:
    case Node{l, i}:
      Bits.low(i)

def fitx.top(fuel: Nat, up: Bool, +mg: Sizes, +x: Node, left: Bool) -> Maybe<&2, Node>:
  match fuel up:
    case 0n _:
      Some{x}
    case 1n+f False{}:
      match left:
        case True{}:
          Some{x}
        case False{}:
          None{}
    case 1n+f True{}:
      +p = Node.parent(x)
      fitx.top(f, fitx.has(mg, Node.parent(p)), mg, p, Bool.and(left, Bool.not(fitx.low(x))))

def fitx.lay.put(m: Maybe<&2, Node>, rest: List<&2, Node>) -> List<&2, Node>:
  match m:
    case None{}:
      rest
    case Some{x}:
      x <> rest

def fitx.lay(v: List<&2, Node>, +fuel: Nat, +mg: Sizes) -> List<&2, Node>:
  match v:
    case Nil{}:
      Nil{}
    case +x <> rest:
      fitx.lay.put(fitx.top(fuel, fitx.has(mg, Node.parent(x)), mg, x, True{}), fitx.lay(rest, fuel, mg))

def fitx.done(+fuel: Nat, v: List<&2, Node>, s: Pass) -> List<&2, Node> & List<&2, Node>:
  match s:
    case Pass{lines, size, acc}:
      (List.reverse(&2, Node, acc), fitx.lay(v, fuel, lines))

# the fuel of a walk up the tree: a node of a tiling of T messages has a
# level below the bits of T
def fitx.run(+t: List<&2, Bool>, +budget: Nat, +info: Info, +v: List<&2, Node>, lines: Sizes, +size: Nat) -> List<&2, Node> & List<&2, Node>:
  +fuel = List.length(&2, Bool, t)
  +ps = fitx.sort(t, Pair.fst(List<&2, Cand>, Sizes, fitx.all(v, fuel, info, (Nil{}, SzEnd{}))))
  fitx.done(fuel, v, fitx.pass(ps, True{}, budget, Pass{lines, size, Nil{}}))

def fitx.if(over: Bool, +t: List<&2, Bool>, +budget: Nat, +info: Info, +v: List<&2, Node>, lines: Sizes, +size: Nat) -> List<&2, Node> & List<&2, Node>:
  match over:
    case False{}:
      (Nil{}, v)
    case True{}:
      fitx.run(t, budget, info, v, lines, size)

def fitx.go(+t: List<&2, Bool>, +budget: Nat, +info: Info, +v: List<&2, Node>, r: Sizes & Nat) -> List<&2, Node> & List<&2, Node>:
  (lines, size) = r
  +z = size
  fitx.if(Nat.is_gt(z, budget), t, budget, info, v, lines, z)

# = fit(Last{}, t, budget, ph, info, v) on a view that tiles 0..T
def fitx(+t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: Info, +v: List<&2, Node>) -> List<&2, Node> & List<&2, Node>:
  fitx.go(t, budget, info, v, fitx.lines(v, ph, info, SzEnd{}, 0n))

# the view after fitx
def fitx.view(+t: List<&2, Bool>, +budget: Nat, +ph: Nat, +info: Info, +v: List<&2, Node>) -> List<&2, Node>:
  Pair.snd(List<&2, Node>, List<&2, Node>, fitx(t, budget, ph, info, v))

# The shipped step
# ----------------
# step with the fast batch: on a state whose two views tile the messages it
# is step itself (law stepx_is_step); the message's grown view is built
# once.

def fitcx.if(over: Bool, +cfg: Cfg, +t: List<&2, Bool>, +info: Info, +cv: List<&2, Node>) -> List<&2, Node>:
  match over:
    case False{}:
      cv
    case True{}:
      fitx.view(t, Cfg.cfloor(cfg), Cfg.ph(cfg), info, cv)

def fitcx(+cfg: Cfg, +t: List<&2, Bool>, +info: Info, +cv: List<&2, Node>) -> List<&2, Node>:
  fitcx.if(Nat.is_gt(view_size(Cfg.ph(cfg), info, cv), Cfg.cceil(cfg)), cfg, t, info, cv)

def msgx.cview(merged: List<&2, Node>, +cfg: Cfg, +t: List<&2, Bool>, +info: Info, +view: List<&2, Node>, +cv: List<&2, Node>) -> List<&2, Node>:
  match merged:
    case Nil{}:
      fitcx(cfg, t, info, cv)
    case h <> rest:
      fitx.view(t, Cfg.cfloor(cfg), Cfg.ph(cfg), info, view)

def msgx.after(+merged: List<&2, Node>, +view: List<&2, Node>, +cfg: Cfg, +t: List<&2, Bool>, +info: Info, +cv: List<&2, Node>, ready: List<&2, Node>, busy: List<&2, Node>) -> St & List<&2, Node>:
  (St{t, info, view, Nat.is_gt(view_size(Cfg.ph(cfg), info, view), Cfg.floor(cfg)), msgx.cview(merged, cfg, t, info, view, cv), ready, busy}, merged)

def msgx.batch(r: List<&2, Node> & List<&2, Node>, +cfg: Cfg, +t: List<&2, Bool>, +info: Info, +cv: List<&2, Node>, ready: List<&2, Node>, busy: List<&2, Node>) -> St & List<&2, Node>:
  (merged, view) = r
  msgx.after(merged, view, cfg, t, info, cv, ready, busy)

def msgx.go(grow: Bool, +cfg: Cfg, +t: List<&2, Bool>, +info: Info, +view: List<&2, Node>, +cv: List<&2, Node>, ready: List<&2, Node>, busy: List<&2, Node>) -> St & List<&2, Node>:
  match grow:
    case False{}:
      (St{t, info, view, False{}, fitcx(cfg, t, info, cv), ready, busy}, Nil{})
    case True{}:
      msgx.batch(fitx(t, Cfg.floor(cfg), Cfg.ph(cfg), info, view), cfg, t, info, cv, ready, busy)

def msgx(+cfg: Cfg, s: St) -> St & List<&2, Node>:
  match s:
    case St{+t, +info, view, shrink, cview, ready, busy}:
      +leaf = Node.leaf(t)
      +g = List.append(&2, Node, view, [leaf])
      msgx.go(Bool.or(shrink, Nat.is_gt(view_size(Cfg.ph(cfg), info, g), Cfg.ceil(cfg))), cfg, Bits.inc(t), info, g, List.append(&2, Node, cview, [leaf]), ready, busy)

def buildx.go(+cfg: Cfg, +n: Node, +info: Info, s: St) -> St:
  match s:
    case St{+t, i0, view, shrink, cview, ready, busy}:
      St{t, info, view, shrink, fitcx(cfg, t, info, cview), ready.note(info, n, Nodes.del(ready, n)), Nodes.del(busy, n)}

def buildx(+cfg: Cfg, +s: St, +n: Node, +size: Nat) -> St:
  buildx.go(cfg, n, Info.set(St.info(s), n, size), s)

def stepx(+cfg: Cfg, +s: St, e: Ev) -> St & List<&2, Node>:
  match e:
    case Msg{}:
      msgx(cfg, s)
    case Build{n, size}:
      (buildx(cfg, s, n, size), Nil{})
    case Start{n}:
      (busy.set(s, Nodes.add(St.busy(s), n)), Nil{})
    case Free{n}:
      (busy.set(s, Nodes.del(St.busy(s), n)), Nil{})
