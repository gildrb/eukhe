# submission: one staged change of a submission's lifecycle (port of
# pi-durable's session batch assembly; the Rust host is
# crates/eukhe-durable/src/session/plans.rs). A submission is an admitted
# user input or passive entry write. An input is queued, then placed at its
# user entry, then done with an answer entry or unanswered; a write is
# queued, then done at its entry or unanswered. A change places a queued
# submission at an entry, answers a placed input, or settles a submission
# unanswered (its reason and detail stay with the host: no rule reads
# them). A settled submission stays as it is whatever the change. Pure: no
# IO, no @unsafe. laws/submission.bend states its laws.

import Base

# Types
# -----

# a submission's lifecycle: its type, status and entries (entry ids)
type Sub is Data:
  InQueued{}
  InPlaced{entry: Nat}
  InAnswered{entry: Nat, answer: Nat}
  InDropped{entry: Maybe<&2, Nat>}
  WrQueued{}
  WrPlaced{entry: Nat}
  WrDropped{}

# a staged change
type Change is Data:
  Place{entry: Nat}
  Answer{answer: Nat}
  Drop{}

# why a change does not apply
type Why is Data:
  NotQueued{}
  NotPlacedInput{}

# the outcome of a change: the submission stays, moves to a new lifecycle,
# or the change is refused
type Out is Data:
  Stays{}
  Moves{next: Sub}
  Refused{why: Why}

# The step
# --------

# a change of a queued input
def queued_input(c: Change) -> Out:
  match c:
    case Place{e}:
      Moves{InPlaced{e}}
    case Answer{a}:
      Refused{NotPlacedInput{}}
    case Drop{}:
      Moves{InDropped{None{}}}

# a change of an input placed at entry e
def placed_input(e: Nat, c: Change) -> Out:
  match c:
    case Place{f}:
      Refused{NotQueued{}}
    case Answer{a}:
      Moves{InAnswered{e, a}}
    case Drop{}:
      Moves{InDropped{Some{e}}}

# a change of a queued write
def queued_write(c: Change) -> Out:
  match c:
    case Place{e}:
      Moves{WrPlaced{e}}
    case Answer{a}:
      Refused{NotPlacedInput{}}
    case Drop{}:
      Moves{WrDropped{}}

# the outcome of change c on submission s
def step(s: Sub, c: Change) -> Out:
  match s:
    case InQueued{}:
      queued_input(c)
    case InPlaced{e}:
      placed_input(e, c)
    case InAnswered{e, a}:
      Stays{}
    case InDropped{m}:
      Stays{}
    case WrQueued{}:
      queued_write(c)
    case WrPlaced{e}:
      Stays{}
    case WrDropped{}:
      Stays{}
