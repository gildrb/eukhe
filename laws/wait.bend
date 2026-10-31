# eukhe: the laws of area wait

import Base
import ../bend/wait.bend as Wt
import ../bend/ffi_wait_race.bend as FWt
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (H6) Every other wait has an exit
# ---------------------------------
# LAWS.bend H6. A wait (bend/wait.bend) sees, one at a time and in
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

# (H6.1) The race runs the wait as a stepper of the compiled Bend core
# --------------------------------------------------------------------
# eukhe's race (crates/eukhe-core/src/memory/service/race.rs `race`) has
# no rule of its own: it opens the stepper bend/ffi_wait_race.bend with its
# deadline (none, or one instant: a wait of one tick), polls its event,
# its cancel and its deadline together, sends what it found ready, and
# ends at the first end the stepper answers. More than one can be ready
# at a poll; the wait takes them as if they came in this order: the
# event, the cancel, then the tick that passes the deadline. However
# tokio's wakeups order the polls, they are the stepper's input: the laws
# below hold for every sequence of polls.
#
# The laws speak of the entry through a speller and a reader built from
# the wire's primitives (bend/wire.bend), not through its own codec.

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

# the signals of every poll of ps, in order
def ww_flat(ps: List<&2, Wt.Polled>) -> List<&2, Wt.Sig>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      List.append(&2, Wt.Sig, ww_sigs(p), ww_flat(rest))

# the wait after it sees xs, one signal at a time (Wt.next)
def ww_after(xs: List<&2, Wt.Sig>, w: Wt.W) -> Wt.W:
  match xs:
    case Nil{}:
      w
    case s <> rest:
      ww_after(rest, Wt.next(w, s))

# a poll as the race writes it: three Bools
def ww_spell(r: Wt.Polled) -> String:
  match r:
    case Wt.Polled{w, c, l}:
      Wr.put_bool(w, Wr.put_bool(c, Wr.put_bool(l, "")))

# a deadline as the race writes it: Maybe<Nat>
def ww_spell_dl(dl: Maybe<&2, Nat>) -> String:
  match dl:
    case None{}:
      Wr.put_nat(0n, "")
    case Some{d}:
      Wr.put_nat(1n, Wr.put_nat(d, ""))

# an end as the race reads it: 0 the event, 1 the deadline, 2 the cancel
def ww_spell_end(e: Wt.End, rest: String) -> String:
  match e:
    case Wt.Arrived{}:
      Wr.put_nat(0n, rest)
    case Wt.Expired{}:
      Wr.put_nat(1n, rest)
    case Wt.Cancelled{}:
      Wr.put_nat(2n, rest)

def ww_spell_ends.items(es: List<&2, Wt.End>) -> String:
  match es:
    case Nil{}:
      ""
    case e <> rest:
      ww_spell_end(e, ww_spell_ends.items(rest))

# the ends of a reply: their count, then each end
def ww_spell_ends(+es: List<&2, Wt.End>) -> String:
  Wr.put_nat(List.length(&2, Wt.End, es), ww_spell_ends.items(es))

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

def ww_read_dl.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{d, s}:
      Wr.Got{Some{d}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ww_read_dl.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      ww_read_dl.some(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def ww_read_dl.go(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{t, s}:
      ww_read_dl.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ww_read_dl.end(whole: Bool, dl: Maybe<&2, Nat>) -> Maybe<&2, Maybe<&2, Nat>>:
  match whole:
    case True{}:
      Some{dl}
    case False{}:
      None{}

def ww_read_dl.whole(d: Wr.Dec<Maybe<&2, Nat>>) -> Maybe<&2, Maybe<&2, Nat>>:
  match d:
    case Wr.Got{dl, s}:
      ww_read_dl.end(Wr.end(s), dl)
    case Wr.Bad{}:
      None{}

# the deadline s is, when s is exactly one deadline
def ww_read_dl(s: String) -> Maybe<&2, Maybe<&2, Nat>>:
  ww_read_dl.whole(ww_read_dl.go(Wr.get_nat(s)))

def ww_state(r: FWt.St & String) -> FWt.St:
  (s, x) = r
  s

def ww_reply(r: FWt.St & String) -> String:
  (s, x) = r
  x

# the stepper after it is sent the polls ps, spelled
def ww_feed(ps: List<&2, Wt.Polled>, st: FWt.St) -> FWt.St:
  match ps:
    case Nil{}:
      st
    case p <> rest:
      ww_feed(rest, ww_state(FWt.step(st, ww_spell(p))))

# the stepper as opened with the deadline dl, spelled
def ww_opened(dl: Maybe<&2, Nat>) -> FWt.St:
  ww_state(FWt.open(ww_spell_dl(dl)))

def ww_new.go(done: List<&2, Wt.End>, later: List<&2, Wt.End>) -> List<&2, Wt.End>:
  match done:
    case Nil{}:
      later
    case e <> t:
      Nil{}

# the ends the poll p brings after the polls pre to a wait with deadline
# dl: what the model's run reports over the signals up to p, when it
# reported nothing before p; else nothing
def ww_new(+dl: Maybe<&2, Nat>, +pre: List<&2, Wt.Polled>, p: Wt.Polled) -> List<&2, Wt.End>:
  ww_new.go(Wt.run(dl, ww_flat(pre)), Wt.run(dl, List.append(&2, Wt.Sig, ww_flat(pre), ww_sigs(p))))

# the deadline the race opens with: one instant (a wait of one tick), or
# none
def ww_race_dl(armed: Bool) -> Maybe<&2, Nat>:
  match armed:
    case True{}:
      Some{1n}
    case False{}:
      None{}

# the end of a race's first poll, written from H6.1 alone: the event wins
# over the cancel and the deadline, the cancel over the deadline; the
# deadline ends it only when it has one; nothing ready ends nothing
def ww_prio.late(l: Bool, armed: Bool) -> List<&2, Wt.End>:
  match l armed:
    case True{} True{}:
      [Wt.Expired{}]
    case True{} False{}:
      Nil{}
    case False{} armed:
      Nil{}

def ww_prio(armed: Bool, r: Wt.Polled) -> List<&2, Wt.End>:
  match r:
    case Wt.Polled{w, c, l}:
      match w c:
        case True{} c:
          [Wt.Arrived{}]
        case False{} True{}:
          [Wt.Cancelled{}]
        case False{} False{}:
          ww_prio.late(l, armed)

# LAW wait_poll_refines: the race opened as eukhe opens it (a deadline of
# one instant, or none) ends at its first poll as H6.1 says: the event wins
# over the cancel and the deadline, the cancel over the deadline, the
# deadline only when there is one, and nothing ends a poll that found
# nothing ready
# EXCLUDES: another priority (a deadline or a cancel that beats a ready
# event), an end with nothing ready, a ready signal ignored (a lost
# wake-up: the race would wait on a finished future)
law wait_poll_refines:
  for +armed: Bool
  for +r: Wt.Polled
  {ww_reply(FWt.step(ww_opened(ww_race_dl(armed)), ww_spell(r))) == ww_spell_ends(ww_prio(armed, r)) : String}

# LAW wait_step_is_model: the stepper opened with any deadline and sent any
# polls, in any order, answers each poll with the ends the model's run
# reports at that poll: the run over the signals of every poll so far,
# when it had reported nothing before; else nothing
# EXCLUDES: an end reported twice or at a later poll, an end lost, an
# end other than the model's, a stepper whose state drifts from the
# model's wait after some order of events
law wait_step_is_model:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Polled>
  for +p: Wt.Polled
  for fits: {LawsBase.wire_mfits(dl) == True{} : Bool}
  {ww_reply(FWt.step(ww_feed(pre, ww_opened(dl)), ww_spell(p))) == ww_spell_ends(ww_new(dl, pre, p)) : String}

# LAW wait_entry_once: whatever polls come between, a race that answered
# an end answers no end again
# EXCLUDES: a second end (a wait that ends twice, a double wake-up), an
# ended wait revived by a later event
law wait_entry_once:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Polled>
  for +p: Wt.Polled
  for +mid: List<&2, Wt.Polled>
  for +q: Wt.Polled
  for fits: {LawsBase.wire_mfits(dl) == True{} : Bool}
  for ended: {String.eq(ww_reply(FWt.step(ww_feed(pre, ww_opened(dl)), ww_spell(p))), "0,") == False{} : Bool}
  {ww_reply(FWt.step(ww_feed(List.append(&2, Wt.Polled, pre, p <> mid), ww_opened(dl)), ww_spell(q))) == "0," : String}

# LAW wait_entry_calm: in every state, a poll that found nothing ready
# ends nothing and leaves the wait as it was
# EXCLUDES: a wake-up that ends the wait or moves its deadline
law wait_entry_calm:
  for +w: Wt.W
  {FWt.step(FWt.Live{w}, ww_spell(Wt.Polled{False{}, False{}, False{}})) == (FWt.Live{w}, "0,") : FWt.St & String}

# LAW wait_entry_answers: in every state, every poll the race spells (three
# Bools from the wire's primitives) moves the wait as the model does, one
# signal at a time in the race's order, and answers the spelled ends the
# model's walk reports
# EXCLUDES: a field misread or swapped (event, cancel, deadline), an end
# other than the model's, a reply in another spelling, a state that is not
# the model's
law wait_entry_answers:
  for +w: Wt.W
  for +r: Wt.Polled
  {FWt.step(FWt.Live{w}, ww_spell(r)) == (FWt.Live{ww_after(ww_sigs(r), w)}, ww_spell_ends(Wt.go(ww_sigs(r), w))) : FWt.St & String}

# LAW wait_entry_reads: in every state, an input the laws' reader reads as
# exactly one poll is answered as that poll spelled
# EXCLUDES: an input read otherwise by the entry than by the wire's grammar
law wait_entry_reads:
  for +w: Wt.W
  for +i: String
  for +r: Wt.Polled
  for got: {ww_read(i) == Some{r} : Maybe<&2, Wt.Polled>}
  {FWt.step(FWt.Live{w}, i) == FWt.step(FWt.Live{w}, ww_spell(r)) : FWt.St & String}

# LAW wait_entry_malformed_exact: in every state, an input the laws'
# reader does not read as exactly one poll (a short or bad Bool, input
# left over) keeps the wait and answers exactly the error form 'E ' +
# "wait: malformed poll"
# EXCLUDES: a guessed poll, a default end, a wait moved by garbage,
# another error text
law wait_entry_malformed_exact:
  for +w: Wt.W
  for +i: String
  for no: {ww_read(i) == None{} : Maybe<&2, Wt.Polled>}
  {FWt.step(FWt.Live{w}, i) == (FWt.Live{w}, SCon{'E', SCon{' ', "wait: malformed poll"}}) : FWt.St & String}

# LAW wait_entry_open: the open with a deadline that fits the wire answers
# the spelled ends the model's run reports before any signal: the expiry
# of a deadline of 0, else nothing
# EXCLUDES: a deadline of 0 that waits, a wait that ends at its open
law wait_entry_open:
  for +dl: Maybe<&2, Nat>
  for fits: {LawsBase.wire_mfits(dl) == True{} : Bool}
  {ww_reply(FWt.open(ww_spell_dl(dl))) == ww_spell_ends(Wt.run(dl, Nil{})) : String}

# LAW wait_entry_open_reads: an open input the laws' reader reads as
# exactly one deadline (the reader reads no Nat past the wire) opens as
# that deadline spelled
# EXCLUDES: an open read otherwise by the entry than by the wire's grammar
law wait_entry_open_reads:
  for +i: String
  for +dl: Maybe<&2, Nat>
  for got: {ww_read_dl(i) == Some{dl} : Maybe<&2, Maybe<&2, Nat>>}
  for fits: {LawsBase.wire_mfits(dl) == True{} : Bool}
  {FWt.open(i) == FWt.open(ww_spell_dl(dl)) : FWt.St & String}

# LAW wait_entry_open_malformed_exact: an open input the laws' reader does
# not read as exactly one deadline opens the refused state and answers
# exactly the error form 'E ' + "wait: malformed open"
# EXCLUDES: a default deadline (none, or expired) for garbage
law wait_entry_open_malformed_exact:
  for +i: String
  for no: {ww_read_dl(i) == None{} : Maybe<&2, Maybe<&2, Nat>>}
  {FWt.open(i) == (FWt.Shut{}, SCon{'E', SCon{' ', "wait: malformed open"}}) : FWt.St & String}

# LAW wait_entry_shut: a refused open answers every step with exactly the
# error form 'E ' + "wait: the open was refused"
# EXCLUDES: a refused stepper that ends a wait
law wait_entry_shut:
  for +i: String
  {FWt.step(FWt.Shut{}, i) == (FWt.Shut{}, SCon{'E', SCon{' ', "wait: the open was refused"}}) : FWt.St & String}

# LAW wait_entry_example: anchor: the bytes the race sends and the replies:
# opens with no deadline, an expired one, one tick, a bad tag, input left
# over; on one tick all three ready, the cancel and the deadline, the
# deadline alone, nothing, a short poll, input left over; the deadline
# with none; an event after the cancel; a step of a refused open
# EXCLUDES: an entry that answers other bytes than the grammar's
law wait_entry_example:
  {[ww_reply(FWt.open("0,")), ww_reply(FWt.open("1,0,")), ww_reply(FWt.open("1,1,")), ww_reply(FWt.open("2,")), ww_reply(FWt.open("0,x"))] == ["0,", "1,1,", "0,", SCon{'E', SCon{' ', "wait: malformed open"}}, SCon{'E', SCon{' ', "wait: malformed open"}}] : List<&2, String>} & {[ww_reply(FWt.step(ww_state(FWt.open("1,1,")), "TTT")), ww_reply(FWt.step(ww_state(FWt.open("1,1,")), "FTT")), ww_reply(FWt.step(ww_state(FWt.open("1,1,")), "FFT")), ww_reply(FWt.step(ww_state(FWt.open("1,1,")), "FFF")), ww_reply(FWt.step(ww_state(FWt.open("1,1,")), "TF")), ww_reply(FWt.step(ww_state(FWt.open("1,1,")), "TFFx")), ww_reply(FWt.step(ww_state(FWt.open("0,")), "FFT")), ww_reply(FWt.step(ww_state(FWt.step(ww_state(FWt.open("1,1,")), "FTF")), "TFF")), ww_reply(FWt.step(ww_state(FWt.open("2,")), "TFF"))] == ["1,0,", "1,2,", "1,1,", "0,", SCon{'E', SCon{' ', "wait: malformed poll"}}, SCon{'E', SCon{' ', "wait: malformed poll"}}, "0,", "0,", SCon{'E', SCon{' ', "wait: the open was refused"}}] : List<&2, String>}

# (H6) The walk the poll laws read, pinned
# ----------------------------------------
# wait_poll_refines and the wait_entry_* laws read the model's walk
# `Wt.go`; the laws above pin only `Wt.run`. A fresh adversary filled `go`
# to hold a fired cancel until the next tick (poll `FTF` answered `0,`):
# `go` is pinned here against a walk written from H6.

# the ends a wait in state w reports while it sees xs: an open wait ends
# at the first event, cancel, or tick that passes its deadline, with that
# end, and reports nothing after; an ended wait reports nothing
# the end e, when it comes to an open wait
def go_spec.at(w: Wt.W, e: Wt.End) -> List<&2, Wt.End>:
  match w:
    case Wt.Over{}:
      Nil{}
    case Wt.Open{left}:
      [e]

def go_spec(xs: List<&2, Wt.Sig>, w: Wt.W) -> List<&2, Wt.End>:
  match xs:
    case Nil{}:
      Nil{}
    case s <> rest:
      match s:
        case Wt.Arrive{}:
          go_spec.at(w, Wt.Arrived{})
        case Wt.Cancel{}:
          go_spec.at(w, Wt.Cancelled{})
        case Wt.Tick{}:
          match w:
            case Wt.Over{}:
              Nil{}
            case Wt.Open{left}:
              match left:
                case None{}:
                  go_spec(rest, Wt.Open{None{}})
                case Some{m}:
                  match m:
                    case 0n:
                      [Wt.Expired{}]
                    case 1n+q:
                      go_spec(rest, Wt.Open{Some{q}})

# LAW wait_go_exact: the model's walk is the walk of H6: from any state, over any signals, it
# reports exactly the first end (the event, the cancel, the tick that passes the deadline) and
# nothing after it, and nothing from an ended wait
# EXCLUDES: a fired cancel or a ready event held for later, an end reported twice, an end after
#   the wait ended, a deadline passed a tick late or early
law wait_go_exact:
  for +xs: List<&2, Wt.Sig>
  for +w: Wt.W
  {Wt.go(xs, w) == go_spec(xs, w) : List<&2, Wt.End>}

# The wait model's run and terms, pinned
# --------------------------------------
# The laws at the top of this file state the wait through `Wt.run`,
# `exits`, `stops` and `once`. A third fresh adversary (SpecCheckLease)
# filled `run` to report no end ever with `exits` and `stops` always true
# and `once` always 0, and every law checked: those laws were vacuous. The
# run and the terms are pinned here.

# a wait with deadline dl (None: none; Some{d}: it passes on the d-th
# tick, at once when d is 0) that sees xs: the first end, as go_spec
def run_spec(dl: Maybe<&2, Nat>, xs: List<&2, Wt.Sig>) -> List<&2, Wt.End>:
  match dl:
    case None{}:
      go_spec(xs, Wt.Open{None{}})
    case Some{d}:
      match d:
        case 0n:
          [Wt.Expired{}]
        case 1n+m:
          go_spec(xs, Wt.Open{Some{m}})

def arrive_spec(xs: List<&2, Wt.Sig>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case s <> rest:
      match s:
        case Wt.Arrive{}:
          True{}
        case Wt.Tick{}:
          arrive_spec(rest)
        case Wt.Cancel{}:
          arrive_spec(rest)

def cancel_spec(xs: List<&2, Wt.Sig>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case s <> rest:
      match s:
        case Wt.Arrive{}:
          cancel_spec(rest)
        case Wt.Tick{}:
          cancel_spec(rest)
        case Wt.Cancel{}:
          True{}

def ticks_spec(xs: List<&2, Wt.Sig>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case s <> rest:
      match s:
        case Wt.Arrive{}:
          ticks_spec(rest)
        case Wt.Tick{}:
          1n+ticks_spec(rest)
        case Wt.Cancel{}:
          ticks_spec(rest)

def reached_spec(dl: Maybe<&2, Nat>, k: Nat) -> Bool:
  match dl:
    case None{}:
      False{}
    case Some{d}:
      Nat.is_le(d, k)

def once_spec(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# LAW wait_run_exact: the model's run is the walk of H6 from the deadline: with no deadline an
# open wait, with a deadline of 0 an expiry at once, else an open wait whose deadline passes on
# the d-th tick
# EXCLUDES: a run that never ends (the laws above vacuous), ends late or early, or ends twice
law wait_run_exact:
  for +dl: Maybe<&2, Nat>
  for +xs: List<&2, Wt.Sig>
  {Wt.run(dl, xs) == run_spec(dl, xs) : List<&2, Wt.End>}

# LAW wait_terms_exact: the model's terms the laws above read mean what they say: an event
# came, a cancel came, the ticks counted, the deadline reached, a stop (a cancel or the
# deadline), an exit (an event or a stop), and how many ends a wait that exits reports
# EXCLUDES: terms that make the laws above vacuous (exits always true, once always 0)
law wait_terms_exact:
  for +dl: Maybe<&2, Nat>
  for +xs: List<&2, Wt.Sig>
  for +k: Nat
  for +b: Bool
  {Wt.has_arrive(xs) == arrive_spec(xs) : Bool} & {Wt.has_cancel(xs) == cancel_spec(xs) : Bool} & {Wt.ticks(xs) == ticks_spec(xs) : Nat} & {Wt.reached(dl, k) == reached_spec(dl, k) : Bool} & {Wt.stops(dl, xs) == Bool.or(cancel_spec(xs), reached_spec(dl, ticks_spec(xs))) : Bool} & {Wt.exits(dl, xs) == Bool.or(arrive_spec(xs), Bool.or(cancel_spec(xs), reached_spec(dl, ticks_spec(xs)))) : Bool} & {Wt.once(b) == once_spec(b) : Nat}
