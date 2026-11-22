# eukhe: the laws of area restart_turn

import Base
import ../bend/restart_turn.bend as Rt
import ../bend/ffi_restart_turn.bend as FRt
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# A run the supervisor interrupted goes on by itself
# --------------------------------------------------
# bend/restart_turn.bend, run as the compiled core by
# bend/ffi_restart_turn.bend (eukhe-bend rules/restart_turn.rs). The
# supervisor kills a worker that stopped answering and gives up one that
# crashed past its restart budget; the worker that reopens the session stops
# the run that hung or crashed and asks what follows (eukhe-daemon
# worker/create.rs), and so does the supervisor at each give-up
# (supervisor/supervision.rs). Every input is free: any count of continues
# made, any last relaunch.
#
# R1: a reopened turn with fewer than 3 automatic continues made continues
#     by itself, as its next continue (made + 1).
# R2: a reopened turn with 3 or more made ends the run with its report,
#     naming the continues made: a crash loop past the cap stops.
# R3: a give-up relaunches the worker exactly when no relaunch of the
#     session is unsettled and none ended its turn at the cap; else the
#     worker is given up.
# R4: the entry answers each request Rust writes (the count made within
#     the wire) with the answer of R1-R3, reads exactly the request and
#     nothing after it, and answers any other input with the exact error
#     form `E restart_turn: malformed request`.
#
# Not pinned here, Rust tests cover it: that Rust counts the continues
# made since the turn's last input of another origin (eukhe-daemon
# worker/interrupted_run_tests.rs
# `an_interrupted_turn_continues_three_times_then_ends`,
# `a_replayed_declaration_continues_once`), and that the supervisor's
# prior follows the replies of its relaunches (supervisor/interrupted_runs.rs
# `a_crash_loop_relaunches_until_its_relaunch_fails_or_its_turn_ends`,
# `a_declaration_rides_each_reopen_until_one_persists_it`).

# Spec helpers
# ------------

# R4: the spelling of a request
def rt_w_req(f: Rt.Fact, rest: String) -> String:
  match f:
    case Rt.Reopened{n}:
      Wr.put_nat(0n, Wr.put_nat(n, rest))
    case Rt.GaveUp{p}:
      match p:
        case Rt.Clear{}:
          Wr.put_nat(1n, rest)
        case Rt.Unsettled{}:
          Wr.put_nat(2n, rest)
        case Rt.Ended{}:
          Wr.put_nat(3n, rest)

# R4: the count made fits the wire
def rt_fit(f: Rt.Fact) -> Bool:
  match f:
    case Rt.Reopened{n}:
      LawsBase.wire_fits(n)
    case Rt.GaveUp{p}:
      True{}

# R4: the spelling of a reply
def rt_w_reply(x: Rt.Next) -> String:
  match x:
    case Rt.Continue{n}:
      Wr.put_nat(0n, Wr.put_nat(n, ""))
    case Rt.End{n}:
      Wr.put_nat(1n, Wr.put_nat(n, ""))
    case Rt.Relaunch{}:
      Wr.put_nat(2n, "")
    case Rt.Retire{}:
      Wr.put_nat(3n, "")

# R3: the last relaunch is Clear
def rt_clear(p: Rt.Prior) -> Bool:
  match p:
    case Rt.Clear{}:
      True{}
    case Rt.Unsettled{}:
      False{}
    case Rt.Ended{}:
      False{}

# Laws: what follows (R1-R3)
# --------------------------

# LAW restart_turn_continues (R1): a reopened turn with fewer than 3
# continues made continues as its next one
# EXCLUDES: a hung turn left stopped, a continue that does not count up
#   (an endless crash loop), a cap other than 3 below it
law restart_turn_continues:
  for +made: Nat
  for below: {Nat.is_lt(made, 3n) == True{} : Bool}
  {Rt.next(Rt.Reopened{made}) == Rt.Continue{1n+made} : Rt.Next}

# LAW restart_turn_ends (R2): a reopened turn with 3 or more continues made
# ends the run, naming the continues made
# EXCLUDES: a crash loop continued past the cap, a cap other than 3 above
#   it, a report with another count
law restart_turn_ends:
  for +made: Nat
  for spent: {Nat.is_lt(made, 3n) == False{} : Bool}
  {Rt.next(Rt.Reopened{made}) == Rt.End{made} : Rt.Next}

# LAW restart_turn_give_up_relaunches (R3): a give-up of a session whose
# last relaunch is Clear relaunches its worker
# EXCLUDES: a crash loop left given up while nobody watches
law restart_turn_give_up_relaunches:
  {Rt.next(Rt.GaveUp{Rt.Clear{}}) == Rt.Relaunch{} : Rt.Next}

# LAW restart_turn_give_up_retires (R3): a give-up of a session whose last
# relaunch never opened it, or ended its turn at the cap, gives the worker
# up
# EXCLUDES: a worker that crashes before it opens the session relaunched
#   forever, a relaunch after the cap
law restart_turn_give_up_retires:
  for p: Rt.Prior
  for h: {rt_clear(p) == False{} : Bool}
  {Rt.next(Rt.GaveUp{p}) == Rt.Retire{} : Rt.Next}

# LAW restart_turn_example (R1-R3): anchor: the first and the last
# continue, the cap, past the cap, each give-up
# EXCLUDES: continues counted from 0, the cap moved
law restart_turn_example:
  {[Rt.next(Rt.Reopened{0n}), Rt.next(Rt.Reopened{2n}), Rt.next(Rt.Reopened{3n}), Rt.next(Rt.Reopened{9n}), Rt.next(Rt.GaveUp{Rt.Clear{}}), Rt.next(Rt.GaveUp{Rt.Unsettled{}}), Rt.next(Rt.GaveUp{Rt.Ended{}})] == [Rt.Continue{1n}, Rt.Continue{3n}, Rt.End{3n}, Rt.End{9n}, Rt.Relaunch{}, Rt.Retire{}, Rt.Retire{}] : List<&2, Rt.Next>}

# Laws: the entry (R4)
# --------------------

# LAW restart_turn_entry_answers (R4): the entry answers every request Rust
# spells (the count made within the wire) with the model's answer, spelled
# EXCLUDES: the facts misread, a default, another reply spelling
law restart_turn_entry_answers:
  for +f: Rt.Fact
  for h: {rt_fit(f) == True{} : Bool}
  {FRt.ffi(rt_w_req(f, "")) == rt_w_reply(Rt.next(f)) : String}

# LAW restart_turn_entry_reads (R4): the entry's decoder reads a spelled
# request back whole and leaves the input after it untouched
# EXCLUDES: a decoder that eats or skips input after the request
law restart_turn_entry_reads:
  for +f: Rt.Fact
  for +rest: String
  for h: {rt_fit(f) == True{} : Bool}
  {FRt.get_req(rt_w_req(f, rest)) == Wr.Got{f, rest} : Wr.Dec<Rt.Fact>}

# LAW restart_turn_entry_exact (R4): every input the entry does not answer
# with the error form is a spelled request that fits the wire
# EXCLUDES: an answer on input that is no request
law restart_turn_entry_exact:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FRt.ffi(s)) == False{} : Bool}
  exs f: Rt.Fact
  {s == rt_w_req(f, "") : String} & {rt_fit(f) == True{} : Bool}

# LAW restart_turn_entry_refuses (R4): every error the entry answers is
# exactly `E restart_turn: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law restart_turn_entry_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FRt.ffi(s)) == True{} : Bool}
  {FRt.ffi(s) == Wr.err("restart_turn: malformed request") : String}

# LAW restart_turn_entry_example (R4): anchor: the wire strings Rust sends
# and the replies it reads; an unknown tag and input left over
# EXCLUDES: tags in another order
law restart_turn_entry_example:
  {[FRt.ffi("0,0,"), FRt.ffi("0,3,"), FRt.ffi("1,"), FRt.ffi("2,"), FRt.ffi("3,"), FRt.ffi("4,"), FRt.ffi("1,0,")] == ["0,1,", "1,3,", "2,", "3,", "3,", Wr.err("restart_turn: malformed request"), Wr.err("restart_turn: malformed request")] : List<&2, String>}
