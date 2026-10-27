# tree: the model of the session tree. One tree
# holds all the state of a session. The journal is a list of records;
# each record changes the tree. Replay of the journal makes the tree
# again; a replay of a prefix is a snapshot.
#
# A node has a key k, a parent key p and a value v. Key 0 is the root: it
# is not a node. A node's parent is the root or a node, and its key is
# more than its parent's key, so the tree has no cycles. The tree is a
# list of nodes in ascending key order.
#
# A record is one of:
#
# - Do{Put{k, p, v}}: set node k. The tree rejects it (and does not
#   change) when p is not less than k, or when p is not the root and not
#   a node.
# - Do{Del{k}}: remove node k and every node below it. The tree rejects
#   Del{0} (and does not change): the root is not a node.
# - Rewind{ops}: set and unset nodes exactly, to go back to an earlier
#   tree. The ops are diff(current, target). The tree rejects the rewind
#   (and does not change) when the result is not a valid tree.
#
# A recursive scan takes the test of its first node as a parameter (Bend
# matches only parameters); `*.at` computes that test.
#
# The Rust tree (crates/eukhe-durable/src/tree/) runs the compiled core
# below (`core.step`); LAWS.bend (S1) proves it is this model.

import Base

# A node
type Ent is Data:
  Ent{k: Nat, p: Nat, v: Nat}

# One change
type Op is Data:
  Put{k: Nat, p: Nat, v: Nat}
  Del{k: Nat}

# One journal record
type Rec is Data:
  Do{op: Op}
  Rewind{ops: List<&2, Op>}

def Ent.k(e: Ent) -> Nat:
  match e:
    case Ent{k, p, v}:
      k

def Ent.p(e: Ent) -> Nat:
  match e:
    case Ent{k, p, v}:
      p

def Ent.v(e: Ent) -> Nat:
  match e:
    case Ent{k, p, v}:
      v

def Ent.eq(a: Ent, b: Ent) -> Bool:
  match a b:
    case Ent{ak, ap, av} Ent{bk, bp, bv}:
      Bool.and(Nat.is_eq(ak, bk), Bool.and(Nat.is_eq(ap, bp), Nat.is_eq(av, bv)))

def Op.k(o: Op) -> Nat:
  match o:
    case Put{k, p, v}:
      k
    case Del{k}:
      k

# Reading
# -------

# the first node of t has key x
def key.at(+t: List<&2, Ent>, +x: Nat) -> Bool:
  match t:
    case Nil{}:
      False{}
    case e <> rest:
      Nat.is_eq(Ent.k(e), x)

# the node with key x; hit is key.at(t, x)
def get.go(t: List<&2, Ent>, +x: Nat, hit: Bool) -> Maybe<&2, Ent>:
  match t:
    case Nil{}:
      None{}
    case e <> +rest:
      match hit:
        case True{}:
          Some{e}
        case False{}:
          get.go(rest, x, key.at(rest, x))

def get(+t: List<&2, Ent>, +x: Nat) -> Maybe<&2, Ent>:
  get.go(t, x, key.at(t, x))

def has(+t: List<&2, Ent>, +x: Nat) -> Bool:
  Maybe.is_some(&2, Ent, get(t, x))

# two lookups give the same node (or both none)
def same(a: Maybe<&2, Ent>, b: Maybe<&2, Ent>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case None{} Some{y}:
      False{}
    case Some{x} None{}:
      False{}
    case Some{x} Some{y}:
      Ent.eq(x, y)

# Writing
# -------

# the order of key x against the first node of t (LT when t is empty)
def first(+x: Nat, +t: List<&2, Ent>) -> Cmp:
  match t:
    case Nil{}:
      LT{}
    case e <> rest:
      Nat.cmp(x, Ent.k(e))

# set node e: insert it in key order, or replace the node with its key;
# c is first(key of e, t)
def set.go(t: List<&2, Ent>, +e: Ent, c: Cmp) -> List<&2, Ent>:
  match t:
    case Nil{}:
      [e]
    case +h <> +rest:
      match c:
        case LT{}:
          e <> h <> rest
        case EQ{}:
          e <> rest
        case GT{}:
          h <> set.go(rest, e, first(Ent.k(e), rest))

def set(+t: List<&2, Ent>, +e: Ent) -> List<&2, Ent>:
  set.go(t, e, first(Ent.k(e), t))

# remove node x (only that node); hit is key.at(t, x)
def unset.go(t: List<&2, Ent>, +x: Nat, hit: Bool) -> List<&2, Ent>:
  match t:
    case Nil{}:
      Nil{}
    case e <> +rest:
      match hit:
        case True{}:
          unset.go(rest, x, key.at(rest, x))
        case False{}:
          e <> unset.go(rest, x, key.at(rest, x))

def unset(+t: List<&2, Ent>, +x: Nat) -> List<&2, Ent>:
  unset.go(t, x, key.at(t, x))

# a node k may hang under p in t
def ok(+t: List<&2, Ent>, +k: Nat, +p: Nat) -> Bool:
  Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), has(t, p)))

def elem(xs: List<&2, Nat>, +x: Nat) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(Nat.is_eq(y, x), elem(rest, x))

# the first node of t is in gone, or its parent is
def gone.at(+t: List<&2, Ent>, +gone: List<&2, Nat>) -> Bool:
  match t:
    case Nil{}:
      False{}
    case +e <> rest:
      Bool.or(elem(gone, Ent.k(e)), elem(gone, Ent.p(e)))

# remove every node whose key is in gone, or whose parent is: a removed
# node's key joins gone. In key order a parent comes before its child.
# hit is gone.at(t, gone).
def prune.go(t: List<&2, Ent>, +gone: List<&2, Nat>, hit: Bool) -> List<&2, Ent>:
  match t:
    case Nil{}:
      Nil{}
    case +e <> +rest:
      match hit:
        case True{}:
          prune.go(rest, Ent.k(e) <> gone, gone.at(rest, Ent.k(e) <> gone))
        case False{}:
          e <> prune.go(rest, gone, gone.at(rest, gone))

# remove node x and every node below it
def prune(+t: List<&2, Ent>, +x: Nat) -> List<&2, Ent>:
  prune.go(t, [x], gone.at(t, [x]))

def put.at(good: Bool, +t: List<&2, Ent>, +e: Ent) -> List<&2, Ent>:
  match good:
    case True{}:
      set(t, e)
    case False{}:
      t

# one change
def step(+t: List<&2, Ent>, o: Op) -> List<&2, Ent>:
  match o:
    case Put{+k, +p, v}:
      put.at(ok(t, k, p), t, Ent{k, p, v})
    case Del{x}:
      match x:
        case 0n:
          t
        case 1n+y:
          prune(t, 1n+y)

# one exact op of a rewind
def exact(+t: List<&2, Ent>, o: Op) -> List<&2, Ent>:
  match o:
    case Put{k, p, v}:
      set(t, Ent{k, p, v})
    case Del{x}:
      unset(t, x)

# a rewind's ops, each exact, in order, from t
def patch(ops: List<&2, Op>, t: List<&2, Ent>) -> List<&2, Ent>:
  match ops:
    case Nil{}:
      t
    case o <> rest:
      patch(rest, exact(t, o))

# Validity
# --------

# k is less than the first key of t
def above(+k: Nat, +t: List<&2, Ent>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case e <> rest:
      Nat.is_lt(k, Ent.k(e))

# every key is less than the one after it
def sorted(t: List<&2, Ent>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +e <> +rest:
      Bool.and(above(Ent.k(e), rest), sorted(rest))

# every node of t hangs under the root or a node of all
def rooted.go(t: List<&2, Ent>, +all: List<&2, Ent>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(ok(all, Ent.k(e), Ent.p(e)), rooted.go(rest, all))

def rooted(+t: List<&2, Ent>) -> Bool:
  rooted.go(t, t)

# a valid tree: sorted and rooted
def sound(+t: List<&2, Ent>) -> Bool:
  Bool.and(sorted(t), rooted(t))

def keep.at(good: Bool, t: List<&2, Ent>, n: List<&2, Ent>) -> List<&2, Ent>:
  match good:
    case True{}:
      n
    case False{}:
      t

# The journal
# -----------

# one record
def apply(+t: List<&2, Ent>, r: Rec) -> List<&2, Ent>:
  match r:
    case Do{o}:
      step(t, o)
    case Rewind{ops}:
      +n = patch(ops, t)
      keep.at(sound(n), t, n)

# the tree after the records rs, from t
def go(rs: List<&2, Rec>, t: List<&2, Ent>) -> List<&2, Ent>:
  match rs:
    case Nil{}:
      t
    case r <> rest:
      go(rest, apply(t, r))

# the tree a journal makes
def replay(rs: List<&2, Rec>) -> List<&2, Ent>:
  go(rs, Nil{})

# Rewind
# ------

# b holds the first node of a
def held.at(+a: List<&2, Ent>, +b: List<&2, Ent>) -> Bool:
  match a:
    case Nil{}:
      False{}
    case e <> rest:
      has(b, Ent.k(e))

# a Del for each node of a that b does not hold; hit is held.at(a, b)
def dels.go(a: List<&2, Ent>, +b: List<&2, Ent>, hit: Bool) -> List<&2, Op>:
  match a:
    case Nil{}:
      Nil{}
    case +e <> +rest:
      match hit:
        case True{}:
          dels.go(rest, b, held.at(rest, b))
        case False{}:
          Del{Ent.k(e)} <> dels.go(rest, b, held.at(rest, b))

def dels(+a: List<&2, Ent>, +b: List<&2, Ent>) -> List<&2, Op>:
  dels.go(a, b, held.at(a, b))

# a holds the first node of b, the same
def kept.at(+a: List<&2, Ent>, +b: List<&2, Ent>) -> Bool:
  match b:
    case Nil{}:
      False{}
    case +e <> rest:
      same(get(a, Ent.k(e)), Some{e})

# a Put for each node of b that a does not hold the same; hit is
# kept.at(a, b)
def puts.go(+a: List<&2, Ent>, b: List<&2, Ent>, hit: Bool) -> List<&2, Op>:
  match b:
    case Nil{}:
      Nil{}
    case +e <> +rest:
      match hit:
        case True{}:
          puts.go(a, rest, kept.at(a, rest))
        case False{}:
          Put{Ent.k(e), Ent.p(e), Ent.v(e)} <> puts.go(a, rest, kept.at(a, rest))

def puts(+a: List<&2, Ent>, +b: List<&2, Ent>) -> List<&2, Op>:
  puts.go(a, b, kept.at(a, b))

# the ops that turn a into b: the removals, then the sets in key order
def diff(+a: List<&2, Ent>, +b: List<&2, Ent>) -> List<&2, Op>:
  List.append(&2, Op, dels(a, b), puts(a, b))

# every op is on a key where a and b differ
def changed(+a: List<&2, Ent>, +b: List<&2, Ent>, ops: List<&2, Op>) -> Bool:
  match ops:
    case Nil{}:
      True{}
    case +o <> rest:
      Bool.and(Bool.not(same(get(a, Op.k(o)), get(b, Op.k(o)))), changed(a, b, rest))

# Delete
# ------

# r drops a node of t only when it is x, or its parent is a node r drops
def only_below(t: List<&2, Ent>, +x: Nat, +r: List<&2, Ent>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Bool.or(has(r, Ent.k(e)), Bool.or(Nat.is_eq(Ent.k(e), x), Bool.and(Bool.not(Nat.is_eq(Ent.p(e), 0n)), Bool.not(has(r, Ent.p(e)))))), only_below(rest, x, r))

# every node of r is a node of t, unchanged
def within(r: List<&2, Ent>, +t: List<&2, Ent>) -> Bool:
  match r:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(same(get(t, Ent.k(e)), Some{e}), within(rest, t))

# The compiled core
# -----------------
# The Rust tree (crates/eukhe-durable/src/tree/) holds one stepper of the
# compiled Bend core (bend/ffi_tree.bend). Its state is the live tree as a
# key map and the journal, so a record costs its change and a lookup, not
# the tree. A node's value is the Rust index of the value: equal values
# get equal indexes. LAWS.bend (S1) states that the core's tree after any
# journal is replay's, that it answers each record as the model decides
# it, and that its rewind plan and snapshot are the model's.

# A key map: a search tree of nodes. A fork holds a split key: its left
# nodes have keys below it, its right nodes keys at or above it. A new
# split halves the key range of its place (the Rust tree's range is
# [0, 2^47)), so a path has at most 47 forks, whatever the order of the
# puts. A fork also holds the largest parent key of its nodes, so a
# delete skips the places where no node can hang under it.
type KMap is Data:
  KNil{}
  KOne{e: Ent}
  KFork{mid: Nat, mp: Nat, l: KMap, r: KMap}

# the largest parent key of the nodes of m (0 for none)
def KMap.mp(+m: KMap) -> Nat:
  match m:
    case KNil{}:
      0n
    case KOne{e}:
      Ent.p(e)
    case KFork{mid, mp, l, r}:
      mp

# a fork, with the largest parent key of its sides
def KMap.fork(+mid: Nat, +l: KMap, +r: KMap) -> KMap:
  KFork{mid, Nat.max(KMap.mp(l), KMap.mp(r)), l, r}

# the nodes of m in key order
def KMap.read(m: KMap) -> List<&2, Ent>:
  match m:
    case KNil{}:
      Nil{}
    case KOne{e}:
      [e]
    case KFork{mid, mp, l, r}:
      List.append(&2, Ent, KMap.read(l), KMap.read(r))

# the nodes of m in key order, then acc
def KMap.onto(m: KMap, acc: List<&2, Ent>) -> List<&2, Ent>:
  match m:
    case KNil{}:
      acc
    case KOne{e}:
      e <> acc
    case KFork{mid, mp, l, r}:
      KMap.onto(l, KMap.onto(r, acc))

# the test of one step down m for key x: at a node, its key is x; at a
# fork, x goes left
def KMap.at(+m: KMap, +x: Nat) -> Bool:
  match m:
    case KNil{}:
      False{}
    case KOne{e}:
      Nat.is_eq(Ent.k(e), x)
    case KFork{mid, mp, l, r}:
      Nat.is_lt(x, mid)

# the node with key x; b is KMap.at(m, x)
def KMap.get.go(m: KMap, +x: Nat, b: Bool) -> Maybe<&2, Ent>:
  match m b:
    case KNil{} True{}:
      None{}
    case KNil{} False{}:
      None{}
    case KOne{e} True{}:
      Some{e}
    case KOne{e} False{}:
      None{}
    case KFork{mid, mp, +l, r} True{}:
      KMap.get.go(l, x, KMap.at(l, x))
    case KFork{mid, mp, l, +r} False{}:
      KMap.get.go(r, x, KMap.at(r, x))

def KMap.get(+m: KMap, +x: Nat) -> Maybe<&2, Ent>:
  KMap.get.go(m, x, KMap.at(m, x))

def KMap.has(+m: KMap, +x: Nat) -> Bool:
  Maybe.is_some(&2, Ent, KMap.get(m, x))

# the half of the key range of a place: the first of hs (the halves of
# the places below it follow)
def KMap.half(hs: List<&2, Nat>) -> Nat:
  match hs:
    case Nil{}:
      0n
    case h <> rest:
      h

def KMap.below(hs: List<&2, Nat>) -> List<&2, Nat>:
  match hs:
    case Nil{}:
      Nil{}
    case h <> rest:
      rest

# two nodes with different keys, split at the larger key; lt: the key of
# a is below the key of b
def KMap.split(+a: Ent, +b: Ent, lt: Bool) -> KMap:
  match lt:
    case True{}:
      KMap.fork(Ent.k(b), KOne{a}, KOne{b})
    case False{}:
      KMap.fork(Ent.k(a), KOne{b}, KOne{a})

# a place for two nodes with different keys. Its keys run from lo below
# lo + 2h, where h is the first of hs (the halves of the places below it
# follow); ca and cb: the key of a, of b is below lo + h. With no half
# left it splits at the larger key.
def KMap.two(hs: List<&2, Nat>, +lo: Nat, +a: Ent, +b: Ent, ca: Bool, cb: Bool) -> KMap:
  match hs:
    case Nil{}:
      KMap.split(a, b, Nat.is_lt(Ent.k(a), Ent.k(b)))
    case +h <> +rest:
      match ca cb:
        case True{} True{}:
          +g = KMap.half(rest)
          KMap.fork(Nat.add(lo, h), KMap.two(rest, lo, a, b, Nat.is_lt(Ent.k(a), Nat.add(lo, g)), Nat.is_lt(Ent.k(b), Nat.add(lo, g))), KNil{})
        case True{} False{}:
          KMap.fork(Nat.add(lo, h), KOne{a}, KOne{b})
        case False{} True{}:
          KMap.fork(Nat.add(lo, h), KOne{b}, KOne{a})
        case False{} False{}:
          +g = KMap.half(rest)
          +n = Nat.add(lo, h)
          KMap.fork(n, KNil{}, KMap.two(rest, n, a, b, Nat.is_lt(Ent.k(a), Nat.add(n, g)), Nat.is_lt(Ent.k(b), Nat.add(n, g))))

# set node e (insert it, or replace the node with its key); hs and lo as
# in two; b is KMap.at(m, key of e)
def KMap.put(m: KMap, +hs: List<&2, Nat>, +lo: Nat, +e: Ent, b: Bool) -> KMap:
  match m b:
    case KNil{} True{}:
      KOne{e}
    case KNil{} False{}:
      KOne{e}
    case KOne{f} True{}:
      KOne{e}
    case KOne{+f} False{}:
      KMap.two(hs, lo, f, e, Nat.is_lt(Ent.k(f), Nat.add(lo, KMap.half(hs))), Nat.is_lt(Ent.k(e), Nat.add(lo, KMap.half(hs))))
    case KFork{mid, mp, +l, r} True{}:
      KMap.fork(mid, KMap.put(l, KMap.below(hs), lo, e, KMap.at(l, Ent.k(e))), r)
    case KFork{+mid, mp, l, +r} False{}:
      KMap.fork(mid, l, KMap.put(r, KMap.below(hs), mid, e, KMap.at(r, Ent.k(e))))

# set node e in m; hs are the halves of the key range, from the top
def KMap.set(+m: KMap, +hs: List<&2, Nat>, +e: Ent) -> KMap:
  KMap.put(m, hs, 0n, e, KMap.at(m, Ent.k(e)))

# remove node x (only that node); b is KMap.at(m, x)
def KMap.unset(m: KMap, +x: Nat, b: Bool) -> KMap:
  match m b:
    case KNil{} True{}:
      KNil{}
    case KNil{} False{}:
      KNil{}
    case KOne{e} True{}:
      KNil{}
    case KOne{e} False{}:
      KOne{e}
    case KFork{mid, mp, +l, r} True{}:
      KMap.fork(mid, KMap.unset(l, x, KMap.at(l, x)), r)
    case KFork{mid, mp, l, +r} False{}:
      KMap.fork(mid, l, KMap.unset(r, x, KMap.at(r, x)))

def KMap.del(+m: KMap, +x: Nat) -> KMap:
  KMap.unset(m, x, KMap.at(m, x))

# remove the nodes of keys ks, one by one
def KMap.drop(ks: List<&2, Nat>, m: KMap) -> KMap:
  match ks:
    case Nil{}:
      m
    case k <> rest:
      KMap.drop(rest, KMap.del(m, k))

# the tests of ups at m: at a node, its key is x or its parent is x or
# more (the node may go); at a fork, gl: x is below the split or a left
# parent is x or more, gr: x is at or above the split or a right parent is
# x or more (the side may hold a node that goes)
def KMap.gl(+m: KMap, +x: Nat) -> Bool:
  match m:
    case KNil{}:
      True{}
    case KOne{e}:
      Bool.or(Nat.is_eq(Ent.k(e), x), Bool.not(Nat.is_lt(Ent.p(e), x)))
    case KFork{mid, mp, l, r}:
      Bool.or(Nat.is_lt(x, mid), Bool.not(Nat.is_lt(KMap.mp(l), x)))

def KMap.gr(+m: KMap, +x: Nat) -> Bool:
  match m:
    case KNil{}:
      True{}
    case KOne{e}:
      True{}
    case KFork{mid, mp, l, r}:
      Bool.or(Bool.not(Nat.is_lt(x, mid)), Bool.not(Nat.is_lt(KMap.mp(r), x)))

# the nodes of m that a delete of x may remove (its node, and the nodes
# with a parent of x or more), in key order, then acc; gl and gr are
# KMap.gl(m, x) and KMap.gr(m, x)
def KMap.ups(m: KMap, +x: Nat, acc: List<&2, Ent>, gl: Bool, gr: Bool) -> List<&2, Ent>:
  match m gl gr:
    case KNil{} _ _:
      acc
    case KOne{e} True{} _:
      e <> acc
    case KOne{e} False{} _:
      acc
    case KFork{mid, mp, +l, +r} True{} True{}:
      KMap.ups(l, x, KMap.ups(r, x, acc, KMap.gl(r, x), KMap.gr(r, x)), KMap.gl(l, x), KMap.gr(l, x))
    case KFork{mid, mp, +l, r} True{} False{}:
      KMap.ups(l, x, acc, KMap.gl(l, x), KMap.gr(l, x))
    case KFork{mid, mp, l, +r} False{} True{}:
      KMap.ups(r, x, acc, KMap.gl(r, x), KMap.gr(r, x))
    case KFork{mid, mp, l, r} False{} False{}:
      acc

# the gone keys of a delete's walk, as a key map (a key k is the node
# Ent{k, 0, 0}): a lookup costs a path, not the keys gone so far
def gone.of(+hs: List<&2, Nat>, +g: KMap, +k: Nat) -> KMap:
  KMap.set(g, hs, Ent{k, 0n, 0n})

# the first node of s, or its parent, is in the gone map g
def gone.in(+s: List<&2, Ent>, +g: KMap) -> Bool:
  match s:
    case Nil{}:
      False{}
    case +e <> rest:
      Bool.or(KMap.has(g, Ent.k(e)), KMap.has(g, Ent.p(e)))

# the keys of the nodes a delete removes from s, in order: a node goes
# when its key or its parent is gone, and then its key is gone (in key
# order a parent comes before its child); hit is gone.in(s, g)
def drops.s(s: List<&2, Ent>, +hs: List<&2, Nat>, +g: KMap, hit: Bool) -> List<&2, Nat>:
  match s:
    case Nil{}:
      Nil{}
    case +e <> +rest:
      match hit:
        case True{}:
          +g2 = gone.of(hs, g, Ent.k(e))
          Ent.k(e) <> drops.s(rest, hs, g2, gone.in(rest, g2))
        case False{}:
          drops.s(rest, hs, g, gone.in(rest, g))

# the keys of the nodes of s a delete of x removes
def drops(+s: List<&2, Ent>, +hs: List<&2, Nat>, +x: Nat) -> List<&2, Nat>:
  +g = gone.of(hs, KNil{}, x)
  drops.s(s, hs, g, gone.in(s, g))

# one exact op of a rewind, on a key map
def KMap.exact(+m: KMap, +hs: List<&2, Nat>, o: Op) -> KMap:
  match o:
    case Put{k, p, v}:
      KMap.set(m, hs, Ent{k, p, v})
    case Del{x}:
      KMap.del(m, x)

# a rewind's ops, each exact, in order, from m
def KMap.patch(ops: List<&2, Op>, +hs: List<&2, Nat>, m: KMap) -> KMap:
  match ops:
    case Nil{}:
      m
    case o <> rest:
      KMap.patch(rest, hs, KMap.exact(m, hs, o))

# every node of s hangs under the root or a node of m
def KMap.hangs(s: List<&2, Ent>, +m: KMap) -> Bool:
  match s:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(Bool.and(Nat.is_lt(Ent.p(e), Ent.k(e)), Bool.or(Nat.is_eq(Ent.p(e), 0n), KMap.has(m, Ent.p(e)))), KMap.hangs(rest, m))

# The answer to a record, or to a question
type Eff is Data:
  Start{k: Nat}
  Stop{k: Nat}
  Restore{k: Nat}

type Ans is Data:
  Kept{}
  Took{}
  Cut{keys: List<&2, Nat>}
  Effects{es: List<&2, Eff>}
  Nodes{es: List<&2, Ent>}

def put.ans(good: Bool, +m: KMap, +hs: List<&2, Nat>, +e: Ent) -> KMap & Ans:
  match good:
    case True{}:
      (KMap.set(m, hs, e), Took{})
    case False{}:
      (m, Kept{})

def keep.ans(good: Bool, m: KMap, n: KMap) -> KMap & Ans:
  match good:
    case True{}:
      (n, Took{})
    case False{}:
      (m, Kept{})

def cut.ans(m: KMap, +ks: List<&2, Nat>) -> KMap & Ans:
  (KMap.drop(ks, m), Cut{ks})

# a delete: key 0 is the root (no change); else the walk over the nodes
# it may remove
def del.ans(+m: KMap, +hs: List<&2, Nat>, x: Nat) -> KMap & Ans:
  match x:
    case 0n:
      (m, Kept{})
    case 1n++y:
      cut.ans(m, drops(KMap.ups(m, 1n+y, Nil{}, KMap.gl(m, 1n+y), KMap.gr(m, 1n+y)), hs, 1n+y))

# one record on a key map, and its answer
def KMap.rec(+m: KMap, +hs: List<&2, Nat>, r: Rec) -> KMap & Ans:
  match r:
    case Do{o}:
      match o:
        case Put{+k, +p, v}:
          put.ans(Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), KMap.has(m, p))), m, hs, Ent{k, p, v})
        case Del{x}:
          del.ans(m, hs, x)
    case Rewind{ops}:
      +n = KMap.patch(ops, hs, m)
      keep.ans(KMap.hangs(KMap.onto(n, Nil{}), n), m, n)

# the key map after the records rs, from m
def KMap.go(rs: List<&2, Rec>, +hs: List<&2, Nat>, m: KMap) -> KMap:
  match rs:
    case Nil{}:
      m
    case r <> rest:
      KMap.go(rest, hs, Pair.fst(KMap, Ans, KMap.rec(m, hs, r)))

# The rewind plan: a merge of two trees in key order
# the first key of s is below k
def below.at(+s: List<&2, Ent>, +k: Nat) -> Bool:
  match s:
    case Nil{}:
      False{}
    case e <> rest:
      Nat.is_lt(Ent.k(e), k)

# s from its first node with a key of k or more; lo is below.at(s, k)
def from.go(s: List<&2, Ent>, +k: Nat, lo: Bool) -> List<&2, Ent>:
  match s:
    case Nil{}:
      Nil{}
    case +e <> +rest:
      match lo:
        case True{}:
          from.go(rest, k, below.at(rest, k))
        case False{}:
          e <> rest

def from.k(+s: List<&2, Ent>, +k: Nat) -> List<&2, Ent>:
  from.go(s, k, below.at(s, k))

def dels.m.at(hit: Bool, +k: Nat, rest: List<&2, Op>) -> List<&2, Op>:
  match hit:
    case True{}:
      rest
    case False{}:
      Del{k} <> rest

# dels(a, b) for a and b in key order: one pass over each
def dels.m(a: List<&2, Ent>, +b: List<&2, Ent>) -> List<&2, Op>:
  match a:
    case Nil{}:
      Nil{}
    case +e <> rest:
      +c = from.k(b, Ent.k(e))
      dels.m.at(key.at(c, Ent.k(e)), Ent.k(e), dels.m(rest, c))

# the first node of s is e
def head.same(+s: List<&2, Ent>, +e: Ent) -> Bool:
  match s:
    case Nil{}:
      False{}
    case f <> rest:
      Ent.eq(f, e)

def puts.m.at(hit: Bool, +e: Ent, rest: List<&2, Op>) -> List<&2, Op>:
  match hit:
    case True{}:
      rest
    case False{}:
      Put{Ent.k(e), Ent.p(e), Ent.v(e)} <> rest

# puts(a, b) for a and b in key order: one pass over each
def puts.m(b: List<&2, Ent>, +a: List<&2, Ent>) -> List<&2, Op>:
  match b:
    case Nil{}:
      Nil{}
    case +e <> rest:
      +c = from.k(a, Ent.k(e))
      puts.m.at(head.same(c, e), e, puts.m(rest, c))

# diff(a, b) for a and b in key order
def diff.m(+a: List<&2, Ent>, +b: List<&2, Ent>) -> List<&2, Op>:
  List.append(&2, Op, dels.m(a, b), puts.m(b, a))

def eff.put(held: Bool, k: Nat) -> Eff:
  match held:
    case True{}:
      Restore{k}
    case False{}:
      Start{k}

# what each op of a rewind of m does to the work of its node: a Del stops
# it; a Put restores a node m has and starts one it does not have
def effects(ops: List<&2, Op>, +m: KMap) -> List<&2, Eff>:
  match ops:
    case Nil{}:
      Nil{}
    case o <> rest:
      match o:
        case Del{k}:
          Stop{k} <> effects(rest, m)
        case Put{+k, p, v}:
          eff.put(KMap.has(m, k), k) <> effects(rest, m)

# The stepper
# the live key map, the journal (newest record first), and the halves of
# the key range, from the top (the Rust tree opens its stepper with
# 2^46, ..., 2, 1, so its keys run in [0, 2^47); the laws hold for any
# halves)
type St is Data:
  St{m: KMap, log: List<&2, Rec>, hs: List<&2, Nat>}

# an event: a record, or a question about the tree after the first n
# records (the rewind plan to it, its nodes)
type Ask is Data:
  Note{r: Rec}
  Plan{n: Nat}
  Snap{n: Nat}

def St.note(log: List<&2, Rec>, +r: Rec, hs: List<&2, Nat>, ma: KMap & Ans) -> St & Ans:
  (m2, a) = ma
  (St{m2, r <> log, hs}, a)

# the key map after the first n records of the journal log
def St.at(+log: List<&2, Rec>, +hs: List<&2, Nat>, n: Nat) -> KMap:
  KMap.go(List.take(&2, Rec, List.reverse(&2, Rec, log), n), hs, KNil{})

def core.step(s: St, q: Ask) -> St & Ans:
  match s:
    case St{+m, +log, +hs}:
      match q:
        case Note{+r}:
          St.note(log, r, hs, KMap.rec(m, hs, r))
        case Plan{n}:
          +a = KMap.onto(m, Nil{})
          (St{m, log, hs}, Effects{effects(diff.m(a, KMap.onto(St.at(log, hs, n), Nil{})), m)})
        case Snap{n}:
          (St{m, log, hs}, Nodes{KMap.onto(St.at(log, hs, n), Nil{})})

def core.start(hs: List<&2, Nat>) -> St:
  St{KNil{}, Nil{}, hs}

# the stepper after the records rs, from s
def core.feed.go(rs: List<&2, Rec>, s: St) -> St:
  match rs:
    case Nil{}:
      s
    case r <> rest:
      core.feed.go(rest, Pair.fst(St, Ans, core.step(s, Note{r})))

def core.feed(hs: List<&2, Nat>, rs: List<&2, Rec>) -> St:
  core.feed.go(rs, core.start(hs))

def St.m(s: St) -> KMap:
  match s:
    case St{m, log, hs}:
      m
