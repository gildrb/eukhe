# throttle: when the streamed partials of one request commit (the Rust
# host is crates/eukhe-durable/src/harness/generation/stream.rs
# `stream_response`). Partials commit as trailing writes, at most one
# commit in flight: a partial with content becomes the pending one and
# arms the timer unless a timer runs or a commit is in flight; the timer
# firing starts a commit of the pending partial (and takes it); a commit
# that settles with a partial pending re-arms the timer; the stop aborts
# the timer and awaits the commit in flight; a dropped request aborts the
# timer. Once stopped, nothing commits and no timer starts.
#
# The model keeps only the four flags; the host keeps the timer's and the
# commit's handles and the pending partial's value, and does exactly the
# actions a step answers. A timer that fires when none runs (one aborted
# as it woke) and a commit that settles when none is in flight change
# nothing. Pure: no IO, no @unsafe. laws/throttle.bend states its laws.

import Base

# Types
# -----

# the throttle: a partial is pending, the timer runs, a commit is in
# flight, the request stopped
type Gate is Data:
  Gate{pending: Bool, timer: Bool, flight: Bool, stopped: Bool}

# what happens to the throttle
type Ev is Data:
  # a partial arrived; shows: it has content
  Part{shows: Bool}
  # the timer fired
  Fire{}
  # the commit in flight settled
  Settle{}
  # the request ended: stop and await the commit in flight
  Finish{}
  # the request was dropped early: stop
  Quit{}

# what the host does
type Act is Data:
  # keep this partial as the pending one
  Keep{}
  # start the timer
  Arm{}
  # start a commit of the pending partial (the host takes it)
  Commit{}
  # abort the timer
  Abort{}
  # await the commit in flight
  Await{}

# a step: the throttle after the event, and the host's actions in order
type Moved is Data:
  Moved{g: Gate, acts: List<&2, Act>}

# The throttle
# ------------

# a throttle that saw nothing
def start() -> Gate:
  Gate{False{}, False{}, False{}, False{}}

# a partial with content before the stop: it is pending; the timer
# starts unless one runs or a commit is in flight
def part.live(t: Bool, f: Bool) -> Moved:
  match t:
    case True{}:
      Moved{Gate{True{}, True{}, f, False{}}, [Keep{}]}
    case False{}:
      match f:
        case True{}:
          Moved{Gate{True{}, False{}, True{}, False{}}, [Keep{}]}
        case False{}:
          Moved{Gate{True{}, True{}, False{}, False{}}, [Keep{}, Arm{}]}

# a partial: one with no content, or one after the stop, changes nothing
def part(s: Bool, shows: Bool, p: Bool, t: Bool, f: Bool) -> Moved:
  match s:
    case True{}:
      Moved{Gate{p, t, f, True{}}, []}
    case False{}:
      match shows:
        case True{}:
          part.live(t, f)
        case False{}:
          Moved{Gate{p, t, f, False{}}, []}

# the timer fired: it no longer runs; the pending partial is taken, and
# a commit of it starts unless the request stopped (or, never with the
# timer running, a commit is in flight: the partial waits for it)
def fire(t: Bool, p: Bool, s: Bool, f: Bool) -> Moved:
  match t:
    case False{}:
      Moved{Gate{p, False{}, f, s}, []}
    case True{}:
      match p:
        case False{}:
          Moved{Gate{False{}, False{}, f, s}, []}
        case True{}:
          match s:
            case True{}:
              Moved{Gate{False{}, False{}, f, True{}}, []}
            case False{}:
              match f:
                case True{}:
                  Moved{Gate{True{}, False{}, True{}, False{}}, []}
                case False{}:
                  Moved{Gate{False{}, False{}, True{}, False{}}, [Commit{}]}

# the commit settled: none is in flight; a pending partial re-arms the
# timer unless the request stopped or a timer runs
def settle(f: Bool, p: Bool, s: Bool, t: Bool) -> Moved:
  match f:
    case False{}:
      Moved{Gate{p, t, False{}, s}, []}
    case True{}:
      match p:
        case False{}:
          Moved{Gate{False{}, t, False{}, s}, []}
        case True{}:
          match s:
            case True{}:
              Moved{Gate{True{}, t, False{}, True{}}, []}
            case False{}:
              match t:
                case True{}:
                  Moved{Gate{True{}, True{}, False{}, False{}}, []}
                case False{}:
                  Moved{Gate{True{}, True{}, False{}, False{}}, [Arm{}]}

# the stop: abort the timer, await the commit in flight
def halt(t: Bool, f: Bool, p: Bool) -> Moved:
  match t:
    case True{}:
      match f:
        case True{}:
          Moved{Gate{p, False{}, False{}, True{}}, [Abort{}, Await{}]}
        case False{}:
          Moved{Gate{p, False{}, False{}, True{}}, [Abort{}]}
    case False{}:
      match f:
        case True{}:
          Moved{Gate{p, False{}, False{}, True{}}, [Await{}]}
        case False{}:
          Moved{Gate{p, False{}, False{}, True{}}, []}

# a dropped request: abort the timer; the commit in flight settles alone
def quit(t: Bool, p: Bool, f: Bool) -> Moved:
  match t:
    case True{}:
      Moved{Gate{p, False{}, f, True{}}, [Abort{}]}
    case False{}:
      Moved{Gate{p, False{}, f, True{}}, []}

# one event
def step(g: Gate, e: Ev) -> Moved:
  match g:
    case Gate{p, t, f, s}:
      match e:
        case Part{shows}:
          part(s, shows, p, t, f)
        case Fire{}:
          fire(t, p, s, f)
        case Settle{}:
          settle(f, p, s, t)
        case Finish{}:
          halt(t, f, p)
        case Quit{}:
          quit(t, p, f)
