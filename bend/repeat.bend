# repeat: the rounds in a row with the same tool calls and the same
# results (docs/harness.md H4.8.4; the Rust host is
# crates/eukhe-durable/src/harness/generation/repeat.rs
# `rounds_in_a_row`). The walk reads the request's context newest first,
# one message at a time, and stops as soon as the row ends. The host
# interns per walk: the calls the reply would make and each round's calls
# (as a set: names and canonical arguments, any order) to an id each, and
# each tool result (its content and error flag) to an id, equal values to
# equal ids; the model decides which messages end the row, how results
# group into rounds, which rounds repeat, and the count with its
# saturation. A system message changes nothing; a result joins the round
# of the next older reply; a reply with calls closes a round: the first
# round repeats when its calls are the requested ones, a later one when
# its calls and its results are the first round's; a user message, a
# reply with no call, a round that does not repeat, or the context's end
# ends the row. The count is 1 and the rounds that repeat, saturated at
# 2^32 - 1. Pure: no IO, no @unsafe. laws/repeat.bend states its laws.

import Base

# Types
# -----

# a message of the context, newest first, as the walk reads it; End: no
# older message
type Ev is Data:
  System{}
  User{}
  # a tool result: its id (content and error flag)
  Result{id: Nat}
  # a reply with tool calls: the id of its calls
  Called{set: Nat}
  # a reply with no tool call
  Said{}
  End{}

# a round: its calls' id and its results' ids, oldest first (context
# order)
type Round is Data:
  Round{set: Nat, results: List<&2, Nat>}

# the walk: the requested calls' id, the rounds that repeat so far, the
# first (newest) round once it repeats, the results read since the last
# reply, oldest first
type Walk is Data:
  Walk{want: Nat, rounds: Nat, first: Maybe<&2, Round>, pend: List<&2, Nat>}

# what one message does
type Next is Data:
  # the row goes on: the walk after the message
  Goes{w: Walk}
  # the row ended: the count
  Stops{count: Nat}

# The count
# ---------

# the largest count: the host's u32 counter saturates there
def cap() -> Nat:
  4294967295n

def count.pick(below: Bool, k: Nat, top: Nat) -> Nat:
  match below:
    case True{}:
      1n+k
    case False{}:
      top

# 1 and the k rounds that repeat, saturated at cap()
def count(+k: Nat) -> Nat:
  count.pick(Nat.is_lt(k, cap()), k, cap())

# The walk
# --------

# a walk of the calls `want` that read nothing yet
def start(want: Nat) -> Walk:
  Walk{want, 0n, None{}, Nil{}}

# the same ids in the same order
def same(a: List<&2, Nat>, b: List<&2, Nat>) -> Bool:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          True{}
        case y <> u:
          False{}
    case x <> t:
      match b:
        case Nil{}:
          False{}
        case y <> u:
          Bool.and(Nat.is_eq(x, y), same(t, u))

# whether the round of calls s and results rs repeats: the first round
# when s is the requested calls, a later one when it is the first round
def repeats(+want: Nat, first: Maybe<&2, Round>, +s: Nat, rs: List<&2, Nat>) -> Bool:
  match first:
    case None{}:
      Nat.is_eq(s, want)
    case Some{r}:
      match r:
        case Round{s0, rs0}:
          Bool.and(Nat.is_eq(s, s0), same(rs, rs0))

# the first round once the round of s and rs repeats
def keep(first: Maybe<&2, Round>, s: Nat, rs: List<&2, Nat>) -> Maybe<&2, Round>:
  match first:
    case None{}:
      Some{Round{s, rs}}
    case Some{r}:
      Some{r}

def called.pick(hit: Bool, +want: Nat, +k: Nat, first: Maybe<&2, Round>, s: Nat, rs: List<&2, Nat>) -> Next:
  match hit:
    case True{}:
      Goes{Walk{want, 1n+k, keep(first, s, rs), Nil{}}}
    case False{}:
      Stops{count(k)}

# one message, newest first
def step(w: Walk, e: Ev) -> Next:
  match w:
    case Walk{+want, +k, +first, +pend}:
      match e:
        case System{}:
          Goes{Walk{want, k, first, pend}}
        case User{}:
          Stops{count(k)}
        case Result{r}:
          Goes{Walk{want, k, first, r <> pend}}
        case Called{+s}:
          called.pick(repeats(want, first, s, pend), want, k, first, s, pend)
        case Said{}:
          Stops{count(k)}
        case End{}:
          Stops{count(k)}
