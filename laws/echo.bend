# eukhe: the laws of area echo

import Base
import ../bend/ffi_echo.bend as FEc

# (B1) The law-free FFI round trip
# --------------------------------
# bend/ffi_echo.bend, entry 0 of the compiled Bend core: no rule of eukhe,
# only the C boundary (crates/eukhe-bend lib.rs tests: text in, text out, a
# state kept in the Bend heap between calls). Every input is free.
#
# E1: the call answers its input, unchanged, the empty text too. No Bend
#     law states E1: the Bend call (FEc.ffi) is the identity by its
#     definition, so any law of it is its unfolding (definitional) and an
#     example of it rests on that unfolding; the bytes across the C boundary
#     (a multi-byte char, the empty text, a large input) no Bend law can
#     see. E1 is tested, not proven: crates/eukhe-bend lib.rs
#     `echo_round_trips` and `echo_round_trips_a_large_input`.
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

# r when m holds an event, else no reply
def ec_if_event(m: Maybe<&2, String>, r: String) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{e}:
      Some{r}

# the event before the i-th (from 0) of evs: nothing before the first
def ec_before(evs: List<&2, String>, i: Nat) -> String:
  match i:
    case 0n:
      ""
    case 1n+j:
      Maybe.default(&2, String, List.get(&2, String, evs, j), "")

# Laws
# ----

# LAW echo_stepper_counts (E2, E3): an open whose input reads as the
# decimal U32 k (Base `U32.read`), fed any events evs, replies first k in
# decimal (Base `U32.show`), then to the i-th event (from 0) the number
# k+1+i in decimal (Base `Nat.show`), a space and the event before it
# (nothing for the first event), and gives no reply past the last event
# EXCLUDES: an open that answers another number or base or echoes its
#   input, a count that does not step by one or restarts, a step that
#   echoes the current event or an older one, a lost space, a reply lost
#   or added
law echo_stepper_counts:
  for +input: String
  for +k: U32
  for read: {U32.read(input) == Some{k} : Maybe<&2, U32>}
  for +evs: List<&2, String>
  for +i: Nat
  {List.get(&2, String, ec_feed(evs, FEc.open(input)), 0n) == Some{U32.show(k)} : Maybe<&2, String>} &
  {List.get(&2, String, ec_feed(evs, FEc.open(input)), 1n+i) == ec_if_event(List.get(&2, String, evs, i), String.append(Nat.show(Nat.add(U32.to_nat(k), 1n+i)), SCon{' ', ec_before(evs, i)})) : Maybe<&2, String>}

# LAW echo_stepper_refused (E2, E3): an open whose input is no decimal U32
# (Base `U32.read` reads none), fed any events evs, replies first
# "E echo: open wants a decimal U32", then to every event
# "E echo: the open was refused", and gives no reply past the last event
# EXCLUDES: a refused open that answers a count or recovers on a later
#   event, a swapped or reworded error text, a reply lost or added
law echo_stepper_refused:
  for +input: String
  for no: {U32.read(input) == None{} : Maybe<&2, U32>}
  for +evs: List<&2, String>
  for +i: Nat
  {List.get(&2, String, ec_feed(evs, FEc.open(input)), 0n) == Some{"E echo: open wants a decimal U32"} : Maybe<&2, String>} &
  {List.get(&2, String, ec_feed(evs, FEc.open(input)), 1n+i) == ec_if_event(List.get(&2, String, evs, i), "E echo: the open was refused") : Maybe<&2, String>}

# LAW echo_example (E2, E3): anchor: Rust's vectors (crates/eukhe-bend lib.rs):
# an open of 5 then the events é and 😀 answer 5, "6 " and "7 é"; an open
# of five is refused and so is its step
# EXCLUDES: a spec that drifts from the Rust tests
law echo_example:
  {ec_feed(["é", "😀"], FEc.open("5")) == ["5", "6 ", "7 é"] : List<&2, String>} &
  {ec_feed(["x"], FEc.open("five")) == ["E echo: open wants a decimal U32", "E echo: the open was refused"] : List<&2, String>}
