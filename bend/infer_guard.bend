# infer_guard: the repetition guard one chunk at a time (bend/infer.bend
# section 4, `guard`, as a stream feeds it: crates/eukhe-ai
# utils/stream_repeat.rs reads a stream's lines and sends each line's id).
# The state is the window k, the chunks read so far (newest first) and
# their count; a chunk either cuts the stream, with the shortest period of
# the window it completes, or is kept. laws/infer_guard.bend pins `feed`
# and that, driven over a stream, it is `guard`; bend/ffi_infer_guard.bend
# runs it as a stepper of the compiled core.

import Base
import ./infer.bend as If

# the guard of one stream: window k, the chunks read (newest first), how
# many
type St is Data:
  St{k: Nat, seen: List<&2, Nat>, n: Nat}

# what one chunk does
type Next is Data:
  Goes{st: St}               # no cut: the guard after the chunk
  Cuts{at: Nat, period: Nat} # cut after `at` chunks; the window's shortest period

# a guard with a window of k chunks that read nothing yet
def start(k: Nat) -> St:
  St{k, Nil{}, 0n}

def shortest.pick(m: Maybe<&2, Nat>, hit: Bool, q: Nat) -> Maybe<&2, Nat>:
  match m:
    case Some{p}:
      Some{p}
    case None{}:
      match hit:
        case True{}:
          Some{1n+q}
        case False{}:
          None{}

# the shortest period 1+q, q < n, whose counter on s reaches k - (1+q)
# (the test `fires.go` makes for each)
def shortest.go(+s: List<&2, Nat>, +k: Nat, n: Nat) -> Maybe<&2, Nat>:
  match n:
    case 0n:
      None{}
    case 1n++q:
      shortest.pick(shortest.go(s, k, q), Nat.is_le(Nat.sub(k, 1n+q), If.cycle(s, q)), q)

# the shortest period of a periodic window ending s (newest first), if
# the guard cuts after s
def shortest(+s: List<&2, Nat>, +k: Nat) -> Maybe<&2, Nat>:
  shortest.go(s, k, If.periods(k))

def feed.of(m: Maybe<&2, Nat>, k: Nat, s: List<&2, Nat>, n: Nat) -> Next:
  match m:
    case None{}:
      Goes{St{k, s, 1n+n}}
    case Some{p}:
      Cuts{1n+n, p}

# the guard reads chunk x
def feed(st: St, x: Nat) -> Next:
  match st:
    case St{+k, seen, n}:
      +s = {x <> seen : List<&2, Nat>}
      feed.of(shortest(s, k), k, s, n)
