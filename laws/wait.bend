# eukhe: the laws of area wait

import Base
import ../bend/wait.bend as Wt
import ../bend/ffi_wait.bend as FWt
import ../bend/wire.bend as Wr

# (H6) Every other wait has an exit
# ---------------------------------
# docs/harness.md H6. A wait (bend/wait.bend) sees, one at a time and in
# any order, its event, ticks of time, and the cancel; dl is its deadline
# in ticks (None: none). The root-turn lease (bend/lease.bend) takes any
# sequence of asks, releases, stops and crashes.

# LAW wait_ends_once: a wait ends exactly once when its event, its cancel or its
# deadline comes, and never otherwise
law wait_ends_once:
  for +dl: Maybe<&2, Nat>
  for +xs: List<&2, Wt.Sig>
  {List.length(&2, Wt.End, Wt.run(dl, xs)) == Wt.once(Wt.exits(dl, xs)) : Nat}

# LAW wait_end_is_final: once the cancel or the deadline came, the wait's end is final:
# what comes after changes nothing
law wait_end_is_final:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Sig>
  for +post: List<&2, Wt.Sig>
  for stop: {Wt.stops(dl, pre) == True{} : Bool}
  {Wt.run(dl, List.append(&2, Wt.Sig, pre, post)) == Wt.run(dl, pre) : List<&2, Wt.End>}

# LAW wait_arrival_wins: an event that comes before the cancel and the deadline ends the
# wait with the event
law wait_arrival_wins:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Sig>
  for +post: List<&2, Wt.Sig>
  for calm: {Wt.exits(dl, pre) == False{} : Bool}
  {Wt.run(dl, List.append(&2, Wt.Sig, pre, Wt.Arrive{} <> post)) == [Wt.Arrived{}] : List<&2, Wt.End>}

# LAW wait_cancel_wins: a cancel that comes before the event and the deadline ends the
# wait as cancelled
law wait_cancel_wins:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Sig>
  for +post: List<&2, Wt.Sig>
  for calm: {Wt.exits(dl, pre) == False{} : Bool}
  {Wt.run(dl, List.append(&2, Wt.Sig, pre, Wt.Cancel{} <> post)) == [Wt.Cancelled{}] : List<&2, Wt.End>}

# (H6.1) The race at one poll runs as the compiled Bend core
# ---------------------------------------------------------
# eukhe's race (crates/eukhe-core/src/memory/service/race.rs `race`)
# polls its event, its cancel and its deadline together and asks the
# entry bend/ffi_wait.bend which of what it found ready ends the race. At
# one poll more than one can be ready; the race takes them as if they
# came in this order: the event, the cancel, then the tick that passes
# the deadline. How tokio's wakeups make up the polls (the interleaving)
# is not a decision: the bridge (bridge/bridge_wait.bend) checks it on
# tokio's paused clock against `Wt.run`.
#
# The laws below speak of the entry through a speller and a reader built
# from the wire's primitives (bend/wire.bend), not through its own codec.

def ww_sig(b: Bool, x: Wt.Sig, rest: List<&2, Wt.Sig>) -> List<&2, Wt.Sig>:
  match b:
    case True{}:
      x <> rest
    case False{}:
      rest

# what a poll found ready, as the signals the model sees, in the order the
# race takes them
def ww_sigs(r: Wt.Polled) -> List<&2, Wt.Sig>:
  match r:
    case Wt.Polled{w, c, l}:
      ww_sig(w, Wt.Arrive{}, ww_sig(c, Wt.Cancel{}, ww_sig(l, Wt.Tick{}, Nil{})))

def ww_first(es: List<&2, Wt.End>) -> Maybe<&2, Wt.End>:
  match es:
    case Nil{}:
      None{}
    case e <> t:
      Some{e}

# the end the model reports when those signals come to an open wait whose
# deadline passes on its next tick (None: it reports none)
def ww_end(r: Wt.Polled) -> Maybe<&2, Wt.End>:
  ww_first(Wt.go(ww_sigs(r), Wt.Open{Some{0n}}))

# a poll as the race writes it: three Bools
def ww_spell(r: Wt.Polled) -> String:
  match r:
    case Wt.Polled{w, c, l}:
      Wr.put_bool(w, Wr.put_bool(c, Wr.put_bool(l, "")))

# an end as the race reads it: 0 none, 1 the event, 2 the cancel, 3 the
# deadline
def ww_spell_end(m: Maybe<&2, Wt.End>) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{e}:
      match e:
        case Wt.Arrived{}:
          Wr.put_nat(1n, "")
        case Wt.Cancelled{}:
          Wr.put_nat(2n, "")
        case Wt.Expired{}:
          Wr.put_nat(3n, "")

def ww_read.late(w: Bool, c: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<Wt.Polled>:
  match r:
    case Wr.Got{l, s}:
      Wr.Got{Wt.Polled{w, c, l}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ww_read.cancel(w: Bool, r: Wr.Dec<Bool>) -> Wr.Dec<Wt.Polled>:
  match r:
    case Wr.Got{c, s}:
      ww_read.late(w, c, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ww_read.go(r: Wr.Dec<Bool>) -> Wr.Dec<Wt.Polled>:
  match r:
    case Wr.Got{w, s}:
      ww_read.cancel(w, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ww_read.end(whole: Bool, r: Wt.Polled) -> Maybe<&2, Wt.Polled>:
  match whole:
    case True{}:
      Some{r}
    case False{}:
      None{}

def ww_read.whole(d: Wr.Dec<Wt.Polled>) -> Maybe<&2, Wt.Polled>:
  match d:
    case Wr.Got{r, s}:
      ww_read.end(Wr.end(s), r)
    case Wr.Bad{}:
      None{}

# the poll s is, when s is exactly one poll
def ww_read(s: String) -> Maybe<&2, Wt.Polled>:
  ww_read.whole(ww_read.go(Wr.get_bool(s)))

# LAW wait_poll_refines: the end of the race at a poll is the end the
# wait model reports when what the poll found ready comes in the order
# event, cancel, deadline: the event wins over the cancel and the
# deadline, the cancel over the deadline, and nothing ends a poll that
# found nothing ready
# EXCLUDES: another priority (a deadline or a cancel that beats a ready
# event), an end with nothing ready, a ready signal ignored
law wait_poll_refines:
  for +r: Wt.Polled
  {Wt.poll(r) == ww_end(r) : Maybe<&2, Wt.End>}

# LAW wait_entry_answers: every poll the race spells (three Bools from the
# wire's primitives) answers the spelled end the model gives
# EXCLUDES: a field misread or swapped (event, cancel, deadline), an end
# other than the model's, a reply in another spelling
law wait_entry_answers:
  for +r: Wt.Polled
  {FWt.ffi(ww_spell(r)) == ww_spell_end(ww_end(r)) : String}

# LAW wait_entry_reads: an input the laws' reader reads as exactly one
# poll answers the spelled end the model gives
# EXCLUDES: an input read otherwise by the entry than by the wire's grammar
law wait_entry_reads:
  for +i: String
  for +r: Wt.Polled
  for got: {ww_read(i) == Some{r} : Maybe<&2, Wt.Polled>}
  {FWt.ffi(i) == ww_spell_end(ww_end(r)) : String}

# LAW wait_entry_malformed_exact: an input the laws' reader does not read
# as exactly one poll (a short or bad Bool, input left over) answers
# exactly the error form 'E ' + "wait: malformed poll"
# EXCLUDES: a guessed poll, a default end, another error text
law wait_entry_malformed_exact:
  for +i: String
  for no: {ww_read(i) == None{} : Maybe<&2, Wt.Polled>}
  {FWt.ffi(i) == SCon{'E', SCon{' ', "wait: malformed poll"}} : String}

# LAW wait_entry_example: anchor: the bytes the race sends and the replies:
# all three ready, the cancel and the deadline, the deadline alone,
# nothing, a short poll, input left over
# EXCLUDES: an entry that answers other bytes than the grammar's
law wait_entry_example:
  {[FWt.ffi("TTT"), FWt.ffi("FTT"), FWt.ffi("FFT"), FWt.ffi("FFF"), FWt.ffi("TF"), FWt.ffi("TFFx")] == ["1,", "2,", "3,", "0,", SCon{'E', SCon{' ', "wait: malformed poll"}}, SCon{'E', SCon{' ', "wait: malformed poll"}}] : List<&2, String>}
