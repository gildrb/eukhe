# kin: who may message whom in an agent tree, and how a message lands.
# Run as the compiled core by bend/ffi_kin.bend (eukhe-bend rules/kin.rs;
# asked by the daemon's agent messaging before a message is routed).
#
# An agent messages only its parent and its own children: the tree is a
# list of edges, each a child and its parent (two columns, paired up to
# the shorter one). A message to itself is refused first; then an edge
# with the sender as child and the target as parent makes the target its
# parent; then an edge the other way makes the target its child; anything
# else is refused. An admitted message always lands in the target's inbox:
# a busy target queues it, an idle one takes it now, a parked one is woken
# and then takes it. Never dropped.
# Pure: no IO, no @unsafe.

import Base

# What the target is, seen from the sender
type Relation is Data:
  Parent{}
  Child{}

# Why a message is refused
type Refusal is Data:
  SelfMessage{}
  NotKin{}

# The decision on a message
type Verdict is Data:
  Admit{relation: Relation}
  Refuse{refusal: Refusal}

# The target agent's state when a message reaches it
type State is Data:
  Busy{}
  Idle{}
  Parked{}

# How an admitted message reaches the target's inbox
type Landing is Data:
  Queue{}
  Deliver{}
  WakeThenDeliver{}

# Decision
# --------

# an edge pairs the child a with the parent b: the columns cs (children)
# and ps (parents), paired up to the shorter one
def has(cs: List<&2, String>, ps: List<&2, String>, +a: String, +b: String) -> Bool:
  match cs ps:
    case Nil{} Nil{}:
      False{}
    case Nil{} Con{p, pt}:
      False{}
    case Con{c, ct} Nil{}:
      False{}
    case Con{c, ct} Con{p, pt}:
      Bool.or(Bool.and(String.eq(c, a), String.eq(p, b)), has(ct, pt, a, b))

def decide.down(y: Bool) -> Verdict:
  match y:
    case True{}:
      Admit{Child{}}
    case False{}:
      Refuse{NotKin{}}

def decide.up(x: Bool, +s: String, +t: String, cs: List<&2, String>, ps: List<&2, String>) -> Verdict:
  match x:
    case True{}:
      Admit{Parent{}}
    case False{}:
      decide.down(has(cs, ps, t, s))

def decide.self(e: Bool, +s: String, +t: String, +cs: List<&2, String>, +ps: List<&2, String>) -> Verdict:
  match e:
    case True{}:
      Refuse{SelfMessage{}}
    case False{}:
      decide.up(has(cs, ps, s, t), s, t, cs, ps)

# the decision on a message from s to t in the tree whose edges are the
# columns cs (children) and ps (parents)
def decide(+s: String, +t: String, +cs: List<&2, String>, +ps: List<&2, String>) -> Verdict:
  decide.self(String.eq(s, t), s, t, cs, ps)

# Landing
# -------

# how an admitted message reaches a target in state st
def land(st: State) -> Landing:
  match st:
    case Busy{}:
      Queue{}
    case Idle{}:
      Deliver{}
    case Parked{}:
      WakeThenDeliver{}

# Texts
# -----

# the text of a refusal
def text(f: Refusal) -> String:
  match f:
    case SelfMessage{}:
      "an agent cannot message itself"
    case NotKin{}:
      "agents message only their parent and their own children"
