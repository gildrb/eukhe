# durable (spec): the session tree (area tree) as S1 states it, restated
# without the code of bend/tree.bend (it uses only its types: a node
# Ent{key, parent, value}, an op, a record, an answer, an effect):
#
# T1: a tree is the list of its nodes in key order. Key 0 is the root, not
#     a node. A node hangs under its parent: the parent key is below the
#     node's key, and it is the root or the key of a node.
# T2: a put of node k under p sets node k (the other nodes stay) when k may
#     hang under p in the tree; else the tree stays.
# T3: a delete of key x > 0 removes node x and every node below it: a node
#     whose parent is removed is removed; the other nodes stay. A delete of
#     the root (0) changes nothing.
# T4: a rewind applies its ops exactly, in order (a put sets its node, a
#     delete unsets only its own key), and is kept only when the result is
#     a valid tree (keys in order, every node hangs under the root or a
#     node); else the tree stays.
# T5: the tree of a journal is its records applied in order to the empty
#     tree.
# T6: the rewind from a to b is: a delete of each node of a whose key b
#     lacks, in key order, then a put of each node of b that a does not
#     hold the same, in key order.
# T7: the answer to a record: a put or a rewind is taken when the tree
#     accepts it, else kept; a delete of the root is kept; any other delete
#     cuts the keys of the nodes it removes, in key order. A plan names, per
#     op of a rewind, the work it does: a delete stops its node, a put
#     restores a node the tree has and starts one it does not.
#
# The laws of area tree (laws/tree.bend) state that the model and the
# entry refine it. A spec: the shipped code never calls it.

import Base
import ../../bend/tree.bend as Tr

# Nodes
# -----

def key(e: Tr.Ent) -> Nat:
  match e:
    case Tr.Ent{k, p, v}:
      k

def parent(e: Tr.Ent) -> Nat:
  match e:
    case Tr.Ent{k, p, v}:
      p

def value(e: Tr.Ent) -> Nat:
  match e:
    case Tr.Ent{k, p, v}:
      v

def get.pick(hit: Bool, e: Tr.Ent, m: Maybe<&2, Tr.Ent>) -> Maybe<&2, Tr.Ent>:
  match hit:
    case True{}:
      Some{e}
    case False{}:
      m

# the node with key x: the first node of t with that key
def get(t: List<&2, Tr.Ent>, +x: Nat) -> Maybe<&2, Tr.Ent>:
  match t:
    case Nil{}:
      None{}
    case +e <> rest:
      get.pick(Nat.is_eq(key(e), x), e, get(rest, x))

# t holds a node with key x
def has(+t: List<&2, Tr.Ent>, +x: Nat) -> Bool:
  Maybe.is_some(&2, Tr.Ent, get(t, x))

# T1: a node k may hang under p in t
def hangs(+t: List<&2, Tr.Ent>, +k: Nat, +p: Nat) -> Bool:
  Bool.and(Nat.is_lt(p, k), Bool.or(Nat.is_eq(p, 0n), has(t, p)))

# m is the node e, field by field
def same(m: Maybe<&2, Tr.Ent>, +e: Tr.Ent) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+x}:
      Bool.and(Nat.is_eq(key(x), key(e)), Bool.and(Nat.is_eq(parent(x), parent(e)), Nat.is_eq(value(x), value(e))))

# Validity (T1)
# -------------

# k is below the first key of t
def first_above(+k: Nat, t: List<&2, Tr.Ent>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case e <> rest:
      Nat.is_lt(k, key(e))

# the keys of t ascend
def ordered(t: List<&2, Tr.Ent>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case +e <> +rest:
      Bool.and(first_above(key(e), rest), ordered(rest))

# every node of s hangs in t
def hung(s: List<&2, Tr.Ent>, +t: List<&2, Tr.Ent>) -> Bool:
  match s:
    case Nil{}:
      True{}
    case +e <> rest:
      Bool.and(hangs(t, key(e), parent(e)), hung(rest, t))

# a valid tree: keys in order, every node hanging under the root or a node
def valid(+t: List<&2, Tr.Ent>) -> Bool:
  Bool.and(ordered(t), hung(t, t))

# Changes
# -------

def keep.if(b: Bool, e: Tr.Ent, r: List<&2, Tr.Ent>) -> List<&2, Tr.Ent>:
  match b:
    case True{}:
      e <> r
    case False{}:
      r

# the nodes of t whose key is not x
def without(t: List<&2, Tr.Ent>, +x: Nat) -> List<&2, Tr.Ent>:
  match t:
    case Nil{}:
      Nil{}
    case +e <> rest:
      keep.if(Bool.not(Nat.is_eq(key(e), x)), e, without(rest, x))

# e goes before the first node of t (it has none, or a larger key)
def ins.first(+e: Tr.Ent, t: List<&2, Tr.Ent>) -> Bool:
  match t:
    case Nil{}:
      True{}
    case h <> rest:
      Nat.is_lt(key(e), key(h))

# e inserted in key order into t; before is ins.first(e, t)
def ins(t: List<&2, Tr.Ent>, +e: Tr.Ent, before: Bool) -> List<&2, Tr.Ent>:
  match t:
    case Nil{}:
      [e]
    case +h <> +rest:
      match before:
        case True{}:
          e <> h <> rest
        case False{}:
          h <> ins(rest, e, ins.first(e, rest))

# T2, T4: node e set: the nodes of other keys, and e, in key order
def put(t: List<&2, Tr.Ent>, +e: Tr.Ent) -> List<&2, Tr.Ent>:
  +w = without(t, key(e))
  ins(w, e, ins.first(e, w))

# T3: y is x or below it: walking up from y (hit says y is x, m is the
# node y), x comes before the root. A parent key is below its node's key,
# so f >= y steps reach the root.
def below(f: Nat, +t: List<&2, Tr.Ent>, +x: Nat, hit: Bool, m: Maybe<&2, Tr.Ent>) -> Bool:
  match f:
    case 0n:
      hit
    case 1n+g:
      match hit:
        case True{}:
          True{}
        case False{}:
          match m:
            case None{}:
              False{}
            case Some{e}:
              match e:
                case Tr.Ent{k, p, v}:
                  match p:
                    case 0n:
                      False{}
                    case 1n++q:
                      below(g, t, x, Nat.is_eq(1n+q, x), get(t, 1n+q))

# T3: a delete of x removes the node y
def gone(+t: List<&2, Tr.Ent>, +x: Nat, +y: Nat) -> Bool:
  below(y, t, x, Nat.is_eq(y, x), get(t, y))

# the nodes of s a delete of x from t keeps
def del.keep(s: List<&2, Tr.Ent>, +t: List<&2, Tr.Ent>, +x: Nat) -> List<&2, Tr.Ent>:
  match s:
    case Nil{}:
      Nil{}
    case +e <> rest:
      keep.if(Bool.not(gone(t, x, key(e))), e, del.keep(rest, t, x))

# T3: a delete of x
def del(+t: List<&2, Tr.Ent>, x: Nat) -> List<&2, Tr.Ent>:
  match x:
    case 0n:
      t
    case 1n+q:
      del.keep(t, t, 1n+q)

# T4: one op of a rewind, exactly
def exact(+t: List<&2, Tr.Ent>, o: Tr.Op) -> List<&2, Tr.Ent>:
  match o:
    case Tr.Put{k, p, v}:
      put(t, Tr.Ent{k, p, v})
    case Tr.Del{x}:
      without(t, x)

# T4: the ops of a rewind, in order, from t
def patch(ops: List<&2, Tr.Op>, t: List<&2, Tr.Ent>) -> List<&2, Tr.Ent>:
  match ops:
    case Nil{}:
      t
    case o <> rest:
      patch(rest, exact(t, o))

def apply.put(ok: Bool, +t: List<&2, Tr.Ent>, +e: Tr.Ent) -> List<&2, Tr.Ent>:
  match ok:
    case True{}:
      put(t, e)
    case False{}:
      t

def apply.keep(ok: Bool, t: List<&2, Tr.Ent>, n: List<&2, Tr.Ent>) -> List<&2, Tr.Ent>:
  match ok:
    case True{}:
      n
    case False{}:
      t

# T2-T4: one record
def apply(+t: List<&2, Tr.Ent>, r: Tr.Rec) -> List<&2, Tr.Ent>:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, v}:
          apply.put(hangs(t, k, p), t, Tr.Ent{k, p, v})
        case Tr.Del{x}:
          del(t, x)
    case Tr.Rewind{ops}:
      +n = patch(ops, t)
      apply.keep(valid(n), t, n)

# T5: the records rs applied in order to t
def go(rs: List<&2, Tr.Rec>, t: List<&2, Tr.Ent>) -> List<&2, Tr.Ent>:
  match rs:
    case Nil{}:
      t
    case r <> rest:
      go(rest, apply(t, r))

# T5: the tree a journal makes
def replay(rs: List<&2, Tr.Rec>) -> List<&2, Tr.Ent>:
  go(rs, Nil{})

# Rewind plans (T6)
# -----------------

def op.if(b: Bool, o: Tr.Op, r: List<&2, Tr.Op>) -> List<&2, Tr.Op>:
  match b:
    case True{}:
      o <> r
    case False{}:
      r

# a delete of each node of s whose key b lacks
def diff.dels(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>) -> List<&2, Tr.Op>:
  match s:
    case Nil{}:
      Nil{}
    case +e <> rest:
      op.if(Bool.not(has(b, key(e))), Tr.Del{key(e)}, diff.dels(rest, b))

# a put of each node of s that a does not hold the same
def diff.puts(+a: List<&2, Tr.Ent>, s: List<&2, Tr.Ent>) -> List<&2, Tr.Op>:
  match s:
    case Nil{}:
      Nil{}
    case +e <> rest:
      op.if(Bool.not(same(get(a, key(e)), e)), Tr.Put{key(e), parent(e), value(e)}, diff.puts(a, rest))

# T6: the rewind from a to b
def diff(+a: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>) -> List<&2, Tr.Op>:
  List.append(&2, Tr.Op, diff.dels(a, b), diff.puts(a, b))

# Answers (T7)
# ------------

def took(ok: Bool) -> Tr.Ans:
  match ok:
    case True{}:
      Tr.Took{}
    case False{}:
      Tr.Kept{}

def key.if(b: Bool, k: Nat, r: List<&2, Nat>) -> List<&2, Nat>:
  match b:
    case True{}:
      k <> r
    case False{}:
      r

# the keys of the nodes of s that b does not hold
def lost(s: List<&2, Tr.Ent>, +b: List<&2, Tr.Ent>) -> List<&2, Nat>:
  match s:
    case Nil{}:
      Nil{}
    case +e <> rest:
      key.if(Bool.not(has(b, key(e))), key(e), lost(rest, b))

# T7: the answer to the record r on the tree t
def answer(+t: List<&2, Tr.Ent>, r: Tr.Rec) -> Tr.Ans:
  match r:
    case Tr.Do{o}:
      match o:
        case Tr.Put{+k, +p, v}:
          took(hangs(t, k, p))
        case Tr.Del{x}:
          match x:
            case 0n:
              Tr.Kept{}
            case 1n+q:
              Tr.Cut{lost(t, del(t, 1n+q))}
    case Tr.Rewind{ops}:
      took(valid(patch(ops, t)))

def effect(held: Bool, k: Nat) -> Tr.Eff:
  match held:
    case True{}:
      Tr.Restore{k}
    case False{}:
      Tr.Start{k}

# T7: the work each op of a rewind of t does
def effects(ops: List<&2, Tr.Op>, +t: List<&2, Tr.Ent>) -> List<&2, Tr.Eff>:
  match ops:
    case Nil{}:
      Nil{}
    case o <> rest:
      match o:
        case Tr.Del{k}:
          Tr.Stop{k} <> effects(rest, t)
        case Tr.Put{+k, p, v}:
          effect(has(t, k), k) <> effects(rest, t)
