# optchat: node(l, i) geometry: start/count/end, leaf, parent, sibling, order, and sorted node sets

import Base
import ./bits.bend as OBits

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
      OBits.shl(l, OBits.Bits.val(i))

# n: how many messages
def Node.count(n: Node) -> Nat:
  match n:
    case Node{l, i}:
      OBits.pow2(l)

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
      Node{1n+l, OBits.Bits.up(i)}

# a and b are the two halves of one parent, a first
def Node.sib(a: Node, b: Node) -> Bool:
  match a b:
    case Node{la, ia} Node{lb, ib}:
      +ja = ia
      +jb = ib
      Bool.and(Nat.is_eq(la, lb), Bool.and(Bool.not(OBits.Bits.low(ja)), Bool.and(OBits.Bits.low(jb), OBits.Bits.eq(OBits.Bits.up(ja), OBits.Bits.up(jb)))))

def Node.eq(a: Node, b: Node) -> Bool:
  match a b:
    case Node{la, ia} Node{lb, ib}:
      Bool.and(Nat.is_eq(la, lb), OBits.Bits.same(ia, ib))

# a before b: by level, then index
def Node.lt(a: Node, b: Node) -> Bool:
  match a b:
    case Node{+la, ia} Node{+lb, ib}:
      Bool.or(Nat.is_lt(la, lb), Bool.and(Nat.is_eq(la, lb), Cmp.is_lt(OBits.Bits.cmp(ia, ib))))

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
