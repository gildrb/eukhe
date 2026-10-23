# wire_flat: lists of lists of Nats as one list of Nats, so an entry's
# request is a record of the wire's Nat lists (bend/wire.bend reads them;
# laws/wire.bend proves their round trip). Each item of an inner
# list is written as 1 + item and each inner list ends with 0:
# [[4], [], [0, 7]] is [5, 0, 0, 1, 8, 0].
#
# The decoder reads the list from its end (a right fold), so each step is
# one item and the recursion is structural: the state is what the items
# after the current one decode to.

import Base

# the items of xs (each 1 + item), its end 0, then rest
def one(xs: List<&2, Nat>, rest: List<&2, Nat>) -> List<&2, Nat>:
  match xs:
    case Nil{}:
      0n <> rest
    case x <> t:
      {1n+x : Nat} <> one(t, rest)

# every list of xss, in order
def flat(xss: List<&2, List<&2, Nat>>) -> List<&2, Nat>:
  match xss:
    case Nil{}:
      Nil{}
    case xs <> t:
      one(xs, flat(t))

# What a suffix decodes to: nothing yet (the empty suffix), or the items
# before the first end mark (`open`) and the lists after it (`done`).
type St is Data:
  Start{}
  Mid{open: List<&2, Nat>, done: List<&2, List<&2, Nat>>}

# the lists a state stands for
def St.lists(st: St) -> List<&2, List<&2, Nat>>:
  match st:
    case Start{}:
      Nil{}
    case Mid{o, d}:
      o <> d

# one more item n in front of a suffix in state st
def step.item(n: Nat, st: St) -> Maybe<&2, St>:
  match n:
    case 0n:
      Some{Mid{Nil{}, St.lists(st)}}
    case 1n+x:
      match st:
        case Start{}:
          None{}
        case Mid{o, d}:
          Some{Mid{x <> o, d}}

def step(n: Nat, m: Maybe<&2, St>) -> Maybe<&2, St>:
  match m:
    case None{}:
      None{}
    case Some{st}:
      step.item(n, st)

def fold(ns: List<&2, Nat>) -> Maybe<&2, St>:
  match ns:
    case Nil{}:
      Some{Start{}}
    case n <> rest:
      step(n, fold(rest))

def unflat.fin(m: Maybe<&2, St>) -> Maybe<&2, List<&2, List<&2, Nat>>>:
  match m:
    case None{}:
      None{}
    case Some{st}:
      Some{St.lists(st)}

# the lists ns spells, or none when an item follows the last end mark
def unflat(ns: List<&2, Nat>) -> Maybe<&2, List<&2, List<&2, Nat>>>:
  unflat.fin(fold(ns))
