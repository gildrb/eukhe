# ffi_wait: the end of eukhe's race at one poll
# (crates/eukhe-core/src/memory/service/race.rs) as an entry of the
# compiled Bend core: bend/wait.bend `poll`. The codec is the wire format
# of bend/wire.bend (crates/eukhe-bend/WIRE.md):
#
#   request  work: Bool, cancel: Bool, late: Bool (the event is ready, the
#            cancel fired, the deadline passed)
#   reply    a Nat: 0 nothing ends the race yet, 1 the event ends it,
#            2 the cancel, 3 the deadline
#
# Any other input, or input left over: the error form. laws/wait.bend
# (wait_entry_*) pins the entry. Pure: no IO, no @unsafe.

import Base
import ./wire.bend as W
import ./wait.bend as M

# Decoder
# -------

def get_ready.late(w: Bool, c: Bool, r: W.Dec<Bool>) -> W.Dec<M.Polled>:
  match r:
    case W.Got{l, s}:
      W.Got{M.Polled{w, c, l}, s}
    case W.Bad{}:
      W.Bad{}

def get_ready.cancel(w: Bool, r: W.Dec<Bool>) -> W.Dec<M.Polled>:
  match r:
    case W.Got{c, s}:
      get_ready.late(w, c, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

def get_ready.go(r: W.Dec<Bool>) -> W.Dec<M.Polled>:
  match r:
    case W.Got{w, s}:
      get_ready.cancel(w, W.get_bool(s))
    case W.Bad{}:
      W.Bad{}

# the poll at the start of s
def get_ready(s: String) -> W.Dec<M.Polled>:
  get_ready.go(W.get_bool(s))

# Encoder
# -------

def put_end(m: Maybe<&2, M.End>) -> String:
  match m:
    case None{}:
      W.put_nat(0n, "")
    case Some{e}:
      match e:
        case M.Arrived{}:
          W.put_nat(1n, "")
        case M.Cancelled{}:
          W.put_nat(2n, "")
        case M.Expired{}:
          W.put_nat(3n, "")

# The entry
# ---------

def fail() -> String:
  W.err("wait: malformed poll")

def run.end(whole: Bool, r: M.Polled) -> String:
  match whole:
    case True{}:
      put_end(M.poll(r))
    case False{}:
      fail()

def run(d: W.Dec<M.Polled>) -> String:
  match d:
    case W.Got{r, s}:
      run.end(W.end(s), r)
    case W.Bad{}:
      fail()

def ffi(input: String) -> String:
  run(get_ready(input))
