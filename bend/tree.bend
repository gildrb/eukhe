# tree: the model of the session tree (docs/harness.md, S1). One tree
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
# The Rust tree (crates/eukhe-durable/src/tree/) is checked against this
# model by the bridge (bend/bridge_tree.bend).

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
