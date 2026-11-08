# kin (spec): who may message whom in an agent tree, and how a message
# lands, restated without the messaging code (bend/kin.bend). The laws of
# area kin (laws/kin.bend) state that the code refines it. A spec: the
# shipped code never calls it.
#
# K1: the tree is a list of links, each a child and its parent: the i-th
#     child with the i-th parent, as many links as the shorter column.
# K2: an agent never messages itself.
# K3: an agent messages only its parent (a link from the sender to the
#     target) and its own children (a link from the target to the
#     sender); the parent link is named when both hold.
# K4: an admitted message is never dropped: a busy target queues it, an
#     idle one takes it at once, a parked one is woken and then takes it.

import Base
import ../../bend/kin.bend as K

# K1: the links
# -------------

# a link of the tree: the child, and its parent
type Link is Data:
  Link{child: String, parent: String}

# the links of the columns cs (children) and ps (parents)
def links(cs: List<&2, String>, ps: List<&2, String>) -> List<&2, Link>:
  match cs ps:
    case Nil{} Nil{}:
      []
    case Nil{} Con{p, pt}:
      []
    case Con{c, ct} Nil{}:
      []
    case Con{c, ct} Con{p, pt}:
      Link{c, p} <> links(ct, pt)

# the link l is the one from the child c to the parent p
def link_is(l: Link, +c: String, +p: String) -> Bool:
  match l:
    case Link{x, y}:
      Bool.and(String.eq(x, c), String.eq(y, p))

# some link of ls goes from the child c to the parent p
def linked(ls: List<&2, Link>, +c: String, +p: String) -> Bool:
  match ls:
    case Nil{}:
      False{}
    case l <> t:
      Bool.or(link_is(l, c, p), linked(t, c, p))

# the tree of the columns cs and ps has the edge from the child c to the
# parent p
def has_edge(cs: List<&2, String>, ps: List<&2, String>, +c: String, +p: String) -> Bool:
  linked(links(cs, ps), c, p)

# the name a is one of xs
def mentions(xs: List<&2, String>, +a: String) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(String.eq(x, a), mentions(t, a))

# K2, K3: the decision
# --------------------

# s may message t: not itself, and t is its parent or its child
def admits(+s: String, +t: String, +cs: List<&2, String>, +ps: List<&2, String>) -> Bool:
  Bool.and(Bool.not(String.eq(s, t)), Bool.or(has_edge(cs, ps, s, t), has_edge(cs, ps, t, s)))

def verdict.child(y: Bool) -> K.Verdict:
  match y:
    case True{}:
      K.Admit{K.Child{}}
    case False{}:
      K.Refuse{K.NotKin{}}

def verdict.parent(x: Bool, +s: String, +t: String, cs: List<&2, String>, ps: List<&2, String>) -> K.Verdict:
  match x:
    case True{}:
      K.Admit{K.Parent{}}
    case False{}:
      verdict.child(has_edge(cs, ps, t, s))

def verdict.self(e: Bool, +s: String, +t: String, +cs: List<&2, String>, +ps: List<&2, String>) -> K.Verdict:
  match e:
    case True{}:
      K.Refuse{K.SelfMessage{}}
    case False{}:
      verdict.parent(has_edge(cs, ps, s, t), s, t, cs, ps)

# the decision on a message from s to t in the tree of cs and ps
def verdict(+s: String, +t: String, +cs: List<&2, String>, +ps: List<&2, String>) -> K.Verdict:
  verdict.self(String.eq(s, t), s, t, cs, ps)

# K4: the landing
# ---------------

# how a message reaches a target in state st
def lands(st: K.State) -> K.Landing:
  match st:
    case K.Busy{}:
      K.Queue{}
    case K.Idle{}:
      K.Deliver{}
    case K.Parked{}:
      K.WakeThenDeliver{}

# the landing l ends with the message in the target's inbox: queued, or
# delivered (after a wake)
def in_inbox(l: K.Landing) -> Bool:
  match l:
    case K.Queue{}:
      True{}
    case K.Deliver{}:
      True{}
    case K.WakeThenDeliver{}:
      True{}
