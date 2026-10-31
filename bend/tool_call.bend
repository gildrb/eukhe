# tool_call: the model of one tool call's journal (call 1-3). The Harness
# (crates/eukhe-durable/src/harness/tool.rs and
# tool/invocation.rs) runs it as the stepper bend/ffi_tool_call.bend: it
# opens the call where it journals the call's start, sends every report the
# tool makes and the end of its execute in the order they come (from any
# thread), and does what each reply says. It keeps what the tool reported
# (output, diagnostics, usage, details); the model decides only what is
# stored and what is journaled when.

import Base

# What the Harness sees of a running call, in arrival order
type Ev is Data:
  Report{}                         # the tool reports: output, a diagnostic, usage, details, a read of its output, a nested call
  End{threw: Bool, aborted: Bool}  # the tool's execute returned (threw: with an error), its signal aborted or not

# How a call ends
type How is Data:
  Finished{}   # with the tool's result
  Failed{}     # with the tool's error: it threw, its signal not aborted
  Cancelled{}  # aborted: the abort handler settles it from the progress board

# What the Harness does with an event
type Act is Data:
  Keep{}           # store the report
  Refuse{}         # refuse the report: the call has ended
  Settle{how: How} # the call ended: journal its settle, as how
  Late{}           # an end after the end: nothing

# The record an open journals
type Rec is Data:
  Began{}    # a first attempt: the slot goes running
  Cleared{}  # a rerun after a restart: the slot's progress is cleared

# A call: taking reports, or ended
type C is Data:
  Taking{}
  Ended{}

# how an execute that threw or not, its signal aborted or not, ends the
# call (`ToolEnding`)
def how(threw: Bool, aborted: Bool) -> How:
  match threw:
    case False{}:
      Finished{}
    case True{}:
      match aborted:
        case True{}:
          Cancelled{}
        case False{}:
          Failed{}

# a call opens taking reports; first says a first attempt
def open(first: Bool) -> C & Rec:
  match first:
    case True{}:
      (Taking{}, Began{})
    case False{}:
      (Taking{}, Cleared{})

# one event: the call after it, and what the Harness does
def step(c: C, e: Ev) -> C & Act:
  match c:
    case Taking{}:
      match e:
        case Report{}:
          (Taking{}, Keep{})
        case End{t, a}:
          (Ended{}, Settle{how(t, a)})
    case Ended{}:
      match e:
        case Report{}:
          (Ended{}, Refuse{})
        case End{t, a}:
          (Ended{}, Late{})
