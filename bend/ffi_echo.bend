import Base
import ./wire.bend as W

# The law-free FFI round-trip entry: no rule of eukhe lives here. It pins the
# C boundary itself (text in, text out; a state kept in the Bend heap between
# calls) for crates/eukhe-bend's tests.

# call: the reply is the input, unchanged.
def ffi(input: String) -> String:
  input

# The stepper's state: the steps taken so far and the last event, or a
# refused open.
type St is Type:
  Echo{n: Nat, last: String}
  Refused{}

def open.start(n: Maybe<&2, U32>) -> St & String:
  match n:
    case Some{+k}:
      (Echo{U32.to_nat(k), ""}, U32.show(k))
    case None{}:
      (Refused{}, W.err("echo: open wants a decimal U32"))

# open: the input is the starting count (a decimal U32); the reply is that
# count. Any other input opens the refused state, with the error reply.
def open(input: String) -> St & String:
  open.start(U32.read(input))

# step: counts the event and keeps it; the reply is the new count, a space
# and the previous event. The refused state answers the error and stays.
def step(s: St, input: String) -> St & String:
  match s:
    case Echo{+n, last}:
      (Echo{(n + 1n : Nat), input}, Nat.show((n + 1n : Nat)) ++ " " ++ last)
    case Refused{}:
      (Refused{}, W.err("echo: the open was refused"))
