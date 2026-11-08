# eukhe: the laws of area echo

import Base
import ../bend/ffi_echo.bend as FEc
import ../bend/wire.bend as Wr

# (B1) The law-free FFI round trip
# --------------------------------
# bend/ffi_echo.bend, entry 0 of the compiled Bend core: no rule of eukhe,
# only the C boundary (crates/eukhe-bend lib.rs tests: text in, text out, a
# state kept in the Bend heap between calls). Every input is free.
#
# E1: the call answers its input, unchanged.
# E2: the stepper's open reads its input as a decimal U32 (Base `U32.read`):
#     a count k answers k in decimal (Base `U32.show`); any other input
#     answers the error form "echo: open wants a decimal U32".
# E3: after an open of k, the i-th step answers k+i in decimal (Base
#     `Nat.show`), a space, then the event of the step before it (nothing
#     for the first step); after a refused open every step answers the error
#     form "echo: the open was refused".

# Spec helpers
# ------------

# the reply r, then the replies of the shipped stepper to the events evs,
# one step each from the state of r
def ec_feed(evs: List<&2, String>, r: FEc.St & String) -> List<&2, String>:
  match evs:
    case Nil{}:
      (st, out) = r
      [out]
    case e <> t:
      (st, out) = r
      out <> ec_feed(t, FEc.step(st, e))

# E3: the replies to evs after n steps counted, last the event before
def ec_counts(evs: List<&2, String>, +n: Nat, last: String) -> List<&2, String>:
  match evs:
    case Nil{}:
      Nil{}
    case e <> t:
      String.append(Nat.show(1n+n), SCon{' ', last}) <> ec_counts(t, 1n+n, e)

# E3: the replies to evs after a refused open
def ec_refused(evs: List<&2, String>) -> List<&2, String>:
  match evs:
    case Nil{}:
      Nil{}
    case e <> t:
      Wr.err("echo: the open was refused") <> ec_refused(t)

# E2, E3: the open's reply, then the steps', for the open's reading m
def ec_spec(m: Maybe<&2, U32>, evs: List<&2, String>) -> List<&2, String>:
  match m:
    case None{}:
      Wr.err("echo: open wants a decimal U32") <> ec_refused(evs)
    case Some{+k}:
      U32.show(k) <> ec_counts(evs, U32.to_nat(k), "")

# Laws
# ----

# LAW echo_ffi_identity (E1): the call answers its input, unchanged
# EXCLUDES: a call that drops, adds, re-encodes or reorders a char (a
#   multi-byte char, the empty input)
law echo_ffi_identity:
  for s: String
  {FEc.ffi(s) == s : String}

# LAW echo_stepper_history (E2, E3): the shipped stepper, opened with any
# input and fed any events, replies to the open and to each event what the
# spec answers
# EXCLUDES: an open that reads another number or base, a count that does
#   not step by one, a step that echoes the current event instead of the
#   one before, a lost space, a refused open that answers a count, a
#   swapped or reworded error text
law echo_stepper_history:
  for +input: String
  for evs: List<&2, String>
  {ec_feed(evs, FEc.open(input)) == ec_spec(U32.read(input), evs) : List<&2, String>}

# LAW echo_example (E1-E3): anchor: Rust's vectors (crates/eukhe-bend lib.rs):
# a text and the empty text call back as themselves; an open of 5 then the
# events é and 😀 answer 5, "6 " and "7 é"; an open of five is refused and
# so is its step
# EXCLUDES: a spec that drifts from the Rust tests
law echo_example:
  {[FEc.ffi("hello"), FEc.ffi("ação 漢 😀 ")] == ["hello", "ação 漢 😀 "] : List<&2, String>} &
  {ec_feed(["é", "😀"], FEc.open("5")) == ["5", "6 ", "7 é"] : List<&2, String>} &
  {ec_feed(["x"], FEc.open("five")) == ["E echo: open wants a decimal U32", "E echo: the open was refused"] : List<&2, String>}
