# eukhe: the laws of area wait

import Base
import ../bend/wait.bend as Wt
import ../bend/ffi_wait_race.bend as FWt
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# Requirements
# ------------
# D4 (spec/README.md D4, "every wait has an exit"; also cited by
# crates/eukhe-bend/src/rules/wait.rs): the requirement this area serves.
# R1 (D4) A wait (bend/wait.bend) sees, one at a time and in any order,
#    its event, ticks of time and the cancel; dl is its deadline in ticks
#    (None: none; Some{d}: it passes on the d-th tick, at once when d is 0).
#    It ends exactly once when its event, its cancel or its deadline comes,
#    and never otherwise; the first of them decides the end, and nothing
#    after it changes the end. Laws: wait_ends_once, wait_end_is_final,
#    wait_arrival_wins, wait_cancel_wins, wait_deadline_wins,
#    wait_go_exact.
# R2 (H6.1, stated in this header) The race runs the wait as a stepper of
#    the compiled Bend core: at each poll it sends what it found ready, and
#    the wait takes them in this order: the event, the cancel, then the
#    tick that passes the deadline; in every state and at every poll.
#    Laws: wait_entry_priority, wait_poll_refines, wait_step_is_model,
#    wait_entry_once, wait_entry_calm.
# R3 (crates/eukhe-bend/WIRE.md, bend/ffi_wait_race.bend) The stepper's
#    wire: an open reads a deadline (Maybe<Nat>), a step reads a poll
#    (three Bools), a reply is a list of ends; an input that is not exactly
#    one poll answers the error form and keeps the wait; an open that is
#    not exactly one deadline opens the refused state, which answers every
#    later step with the error form. Laws: wait_entry_open,
#    wait_entry_open_reads_only, wait_entry_open_refused,
#    wait_entry_reads_only_polls, wait_entry_malformed_keeps,
#    wait_entry_refused_stays; anchor wait_entry_example.

# (D4) Every wait has an exit
# ---------------------------
# The laws of R1 speak of the wait through the laws' own words for what a
# list of signals holds: whether it holds a signal (ww_has), how many of a
# signal it holds (ww_count), whether that many ticks pass a deadline
# (ww_passed); not through the model's terms.

# the two signals are the same signal
def ww_sig_eq(a: Wt.Sig, b: Wt.Sig) -> Bool:
  match a b:
    case Wt.Arrive{} Wt.Arrive{}:
      True{}
    case Wt.Arrive{} Wt.Tick{}:
      False{}
    case Wt.Arrive{} Wt.Cancel{}:
      False{}
    case Wt.Tick{} Wt.Arrive{}:
      False{}
    case Wt.Tick{} Wt.Tick{}:
      True{}
    case Wt.Tick{} Wt.Cancel{}:
      False{}
    case Wt.Cancel{} Wt.Arrive{}:
      False{}
    case Wt.Cancel{} Wt.Tick{}:
      False{}
    case Wt.Cancel{} Wt.Cancel{}:
      True{}

# xs holds the signal x
def ww_has(+x: Wt.Sig, xs: List<&2, Wt.Sig>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case s <> rest:
      Bool.or(ww_sig_eq(x, s), ww_has(x, rest))

# 1 for True, 0 for False
def ww_bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

# one more than n when b holds, else n
def ww_count.add(b: Bool, +n: Nat) -> Nat:
  match b:
    case True{}:
      1n+n
    case False{}:
      n

# how many times xs holds the signal x
def ww_count(+x: Wt.Sig, xs: List<&2, Wt.Sig>) -> Nat:
  match xs:
    case Nil{}:
      0n
    case s <> rest:
      ww_count.add(ww_sig_eq(x, s), ww_count(x, rest))

# n ticks pass the deadline dl: a deadline of d ticks passes on the d-th
def ww_passed(dl: Maybe<&2, Nat>, n: Nat) -> Bool:
  match dl:
    case None{}:
      False{}
    case Some{d}:
      Nat.is_le(d, n)

# xs holds a cancel, or ticks enough to pass the deadline
def ww_stops(+dl: Maybe<&2, Nat>, +xs: List<&2, Wt.Sig>) -> Bool:
  Bool.or(ww_has(Wt.Cancel{}, xs), ww_passed(dl, ww_count(Wt.Tick{}, xs)))

# xs holds something that ends the wait: the event, a cancel, the deadline
def ww_exits(+dl: Maybe<&2, Nat>, +xs: List<&2, Wt.Sig>) -> Bool:
  Bool.or(ww_has(Wt.Arrive{}, xs), ww_stops(dl, xs))

# LAW wait_ends_once (R1): a wait with any deadline that sees any signals reports exactly one end when they hold its event, a cancel, or ticks enough to pass its deadline (a deadline of 0 always), and no end otherwise
# EXCLUDES: a wait that never ends, ends twice, or ends with nothing come
law wait_ends_once:
  for +dl: Maybe<&2, Nat>
  for +xs: List<&2, Wt.Sig>
  {List.length(&2, Wt.End, Wt.run(dl, xs)) == ww_bit(ww_exits(dl, xs)) : Nat}

# LAW wait_end_is_final (R1): once the cancel or the deadline came (a prefix holds a cancel, or ticks enough to pass the deadline), what comes after changes nothing
# EXCLUDES: an end revised or added by a later signal
law wait_end_is_final:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Sig>
  for +post: List<&2, Wt.Sig>
  for stop: {ww_stops(dl, pre) == True{} : Bool}
  {Wt.run(dl, List.append(&2, Wt.Sig, pre, post)) == Wt.run(dl, pre) : List<&2, Wt.End>}

# LAW wait_arrival_wins (R1): an event that comes before any cancel and before the deadline passes ends the wait with the event, whatever follows
# EXCLUDES: an event lost or beaten by a later cancel or tick
law wait_arrival_wins:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Sig>
  for +post: List<&2, Wt.Sig>
  for calm: {ww_exits(dl, pre) == False{} : Bool}
  {Wt.run(dl, List.append(&2, Wt.Sig, pre, Wt.Arrive{} <> post)) == [Wt.Arrived{}] : List<&2, Wt.End>}

# LAW wait_cancel_wins (R1): a cancel that comes before the event and before the deadline passes ends the wait as cancelled, whatever follows
# EXCLUDES: a cancel lost or beaten by a later event or tick
law wait_cancel_wins:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Sig>
  for +post: List<&2, Wt.Sig>
  for calm: {ww_exits(dl, pre) == False{} : Bool}
  {Wt.run(dl, List.append(&2, Wt.Sig, pre, Wt.Cancel{} <> post)) == [Wt.Cancelled{}] : List<&2, Wt.End>}

# LAW wait_deadline_wins (R1): signals with no event and no cancel whose ticks pass the deadline (d ticks or more for a deadline of d; nothing at all for a deadline of 0) end the wait as expired, whatever follows. With wait_ends_once, wait_arrival_wins and wait_cancel_wins this pins the run of every deadline over every signals: the first of the event, the cancel and the deadline decides it
# EXCLUDES: a deadline passed a tick late or early, a deadline of 0 that
#   waits, a deadline beaten by a later event or cancel, an expiry with no
#   deadline
law wait_deadline_wins:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Sig>
  for +post: List<&2, Wt.Sig>
  for quiet: {Bool.or(ww_has(Wt.Arrive{}, pre), ww_has(Wt.Cancel{}, pre)) == False{} : Bool}
  for due: {ww_passed(dl, ww_count(Wt.Tick{}, pre)) == True{} : Bool}
  {Wt.run(dl, List.append(&2, Wt.Sig, pre, post)) == [Wt.Expired{}] : List<&2, Wt.End>}

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
# The laws speak of the entry through a speller built from the wire's
# primitives (bend/wire.bend), not through its own codec.

# the order H6.1 states: the event, the cancel, then the tick
def ww_order() -> List<&2, Wt.Sig>:
  [Wt.Arrive{}, Wt.Cancel{}, Wt.Tick{}]

# the poll r found the signal s ready
def ww_ready(r: Wt.Polled, s: Wt.Sig) -> Bool:
  match r:
    case Wt.Polled{w, c, l}:
      match s:
        case Wt.Arrive{}:
          w
        case Wt.Cancel{}:
          c
        case Wt.Tick{}:
          l

def ww_keep(b: Bool, s: Wt.Sig, rest: List<&2, Wt.Sig>) -> List<&2, Wt.Sig>:
  match b:
    case True{}:
      s <> rest
    case False{}:
      rest

# the signals of xs that the poll r found ready, in the order of xs
def ww_pick(+r: Wt.Polled, xs: List<&2, Wt.Sig>) -> List<&2, Wt.Sig>:
  match xs:
    case Nil{}:
      Nil{}
    case +s <> rest:
      ww_keep(ww_ready(r, s), s, ww_pick(r, rest))

# what a poll found ready, as the signals the model sees: H6.1's order,
# kept where ready
def ww_sigs(+r: Wt.Polled) -> List<&2, Wt.Sig>:
  ww_pick(r, ww_order())

# the signals of every poll of ps, in order
def ww_flat(ps: List<&2, Wt.Polled>) -> List<&2, Wt.Sig>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> rest:
      List.append(&2, Wt.Sig, ww_sigs(p), ww_flat(rest))

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

# the error forms of the stepper
def ww_bad_poll() -> String:
  SCon{'E', SCon{' ', "wait: malformed poll"}}

def ww_bad_open() -> String:
  SCon{'E', SCon{' ', "wait: malformed open"}}

def ww_refused() -> String:
  SCon{'E', SCon{' ', "wait: the open was refused"}}

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

# the replies of the stepper st to the step inputs ins, in order
def ww_replies(ins: List<&2, String>, +st: FWt.St) -> List<&2, String>:
  match ins:
    case Nil{}:
      Nil{}
    case +i <> rest:
      ww_reply(FWt.step(st, i)) <> ww_replies(rest, ww_state(FWt.step(st, i)))

# n copies of e
def ww_copies(n: Nat, +e: String) -> List<&2, String>:
  match n:
    case 0n:
      Nil{}
    case 1n+k:
      e <> ww_copies(k, e)

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

# the stepper after one tick of an open wait whose deadline passes on the
# (m + 1)-th tick from now (left = Some{m}; None: no deadline)
def ww_tick_spec(left: Maybe<&2, Nat>) -> FWt.St & String:
  match left:
    case None{}:
      (FWt.Live{Wt.Open{None{}}}, ww_spell_ends(Nil{}))
    case Some{m}:
      match m:
        case 0n:
          (FWt.Live{Wt.Over{}}, ww_spell_ends([Wt.Expired{}]))
        case 1n+q:
          (FWt.Live{Wt.Open{Some{q}}}, ww_spell_ends(Nil{}))

# one poll, written from H6.1: an ended wait ends nothing more; an open
# one ends with the event when the event is ready, else with the cancel
# when the cancel fired, else it takes one tick when the deadline's timer
# fired, else nothing changes
def ww_poll_spec(w: Wt.W, r: Wt.Polled) -> FWt.St & String:
  match w:
    case Wt.Over{}:
      (FWt.Live{Wt.Over{}}, ww_spell_ends(Nil{}))
    case Wt.Open{left}:
      match r:
        case Wt.Polled{a, c, l}:
          match a:
            case True{}:
              (FWt.Live{Wt.Over{}}, ww_spell_ends([Wt.Arrived{}]))
            case False{}:
              match c:
                case True{}:
                  (FWt.Live{Wt.Over{}}, ww_spell_ends([Wt.Cancelled{}]))
                case False{}:
                  match l:
                    case True{}:
                      ww_tick_spec(left)
                    case False{}:
                      (FWt.Live{Wt.Open{left}}, ww_spell_ends(Nil{}))

# LAW wait_entry_priority (R2): in every state of the wait, every poll the race spells (three Bools from the wire's primitives) moves the wait and answers as H6.1 says: an ended wait answers no end and stays ended; an open one ends with the event when the event is ready, else with the cancel when the cancel fired, else takes one tick when the deadline's timer fired (expiring when that tick passes the deadline), else stays as it was and answers no end
# EXCLUDES: another priority at any poll (a cancel or a deadline that
#   beats a ready event, a deadline that beats a fired cancel), a field
#   misread or swapped, an ended wait revived, a tick lost or counted
#   twice, a reply in another spelling
law wait_entry_priority:
  for +w: Wt.W
  for +r: Wt.Polled
  {FWt.step(FWt.Live{w}, ww_spell(r)) == ww_poll_spec(w, r) : FWt.St & String}

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

# LAW wait_entry_reads_only_polls (R3): in every state of the wait, an input whose answer is not an error form is exactly the spelling of one poll (three Bools, nothing after them)
# EXCLUDES: a decoder that accepts a short or bad Bool or input left over
#   and answers it with ends (a guessed poll, a default end)
law wait_entry_reads_only_polls:
  for +w: Wt.W
  for +s: String
  for other: {LawsBase.wire_opens_err(ww_reply(FWt.step(FWt.Live{w}, s))) == False{} : Bool}
  exs r: Wt.Polled
  {s == ww_spell(r) : String}

# LAW wait_entry_malformed_keeps (R3): in every state of the wait, an input answered with an error form (by wait_entry_reads_only_polls every input that is not exactly one poll) keeps the wait and answers exactly the error form 'E ' + "wait: malformed poll"
# EXCLUDES: a wait moved or ended by garbage, another error text
law wait_entry_malformed_keeps:
  for +w: Wt.W
  for +s: String
  for bad: {LawsBase.wire_opens_err(ww_reply(FWt.step(FWt.Live{w}, s))) == True{} : Bool}
  {FWt.step(FWt.Live{w}, s) == (FWt.Live{w}, ww_bad_poll()) : FWt.St & String}

# LAW wait_entry_open: the open with a deadline that fits the wire answers
# the spelled ends the model's run reports before any signal: the expiry
# of a deadline of 0, else nothing
# EXCLUDES: a deadline of 0 that waits, a wait that ends at its open
law wait_entry_open:
  for +dl: Maybe<&2, Nat>
  for fits: {LawsBase.wire_mfits(dl) == True{} : Bool}
  {ww_reply(FWt.open(ww_spell_dl(dl))) == ww_spell_ends(Wt.run(dl, Nil{})) : String}

# LAW wait_entry_open_reads_only (R3): an open input whose answer is not an error form is exactly the spelling of one deadline that fits the wire (a tag, then the ticks for Some), nothing after it
# EXCLUDES: an open decoder that accepts an unknown tag, a Nat past the
#   wire or input left over and opens a wait on it (a default deadline)
law wait_entry_open_reads_only:
  for +s: String
  for other: {LawsBase.wire_opens_err(ww_reply(FWt.open(s))) == False{} : Bool}
  exs dl: Maybe<&2, Nat>
  {(s, LawsBase.wire_mfits(dl)) == (ww_spell_dl(dl), True{}) : String & Bool}

# LAW wait_entry_open_refused (R3): an open input answered with an error form (by wait_entry_open_reads_only every input that is not exactly one deadline) opens the refused state and answers exactly the error form 'E ' + "wait: malformed open"
# EXCLUDES: a default deadline (none, or expired) opened for garbage,
#   another error text
law wait_entry_open_refused:
  for +s: String
  for bad: {LawsBase.wire_opens_err(ww_reply(FWt.open(s))) == True{} : Bool}
  {FWt.open(s) == (FWt.Shut{}, ww_bad_open()) : FWt.St & String}

# LAW wait_entry_refused_stays (R3): after a refused open, every later step input, in any number and any order, answers exactly the error form 'E ' + "wait: the open was refused": no step after a refused open ends a wait
# EXCLUDES: a refused stepper that ends a wait, revives, or answers ends
law wait_entry_refused_stays:
  for +s: String
  for +ins: List<&2, String>
  for bad: {LawsBase.wire_opens_err(ww_reply(FWt.open(s))) == True{} : Bool}
  {ww_replies(ins, ww_state(FWt.open(s))) == ww_copies(List.length(&2, String, ins), ww_refused()) : List<&2, String>}

# LAW wait_entry_example: anchor: the bytes the race sends and the replies:
# opens with no deadline, an expired one, one tick, a bad tag, input left
# over; on one tick all three ready, the cancel and the deadline, the
# deadline alone, nothing, a short poll, input left over; the deadline
# with none; an event after the cancel; a step of a refused open
# EXCLUDES: an entry that answers other bytes than the grammar's
law wait_entry_example:
  {[ww_reply(FWt.open("0,")), ww_reply(FWt.open("1,0,")), ww_reply(FWt.open("1,1,")), ww_reply(FWt.open("2,")), ww_reply(FWt.open("0,x"))] == ["0,", "1,1,", "0,", SCon{'E', SCon{' ', "wait: malformed open"}}, SCon{'E', SCon{' ', "wait: malformed open"}}] : List<&2, String>} & {[ww_reply(FWt.step(ww_state(FWt.open("1,1,")), "TTT")), ww_reply(FWt.step(ww_state(FWt.open("1,1,")), "FTT")), ww_reply(FWt.step(ww_state(FWt.open("1,1,")), "FFT")), ww_reply(FWt.step(ww_state(FWt.open("1,1,")), "FFF")), ww_reply(FWt.step(ww_state(FWt.open("1,1,")), "TF")), ww_reply(FWt.step(ww_state(FWt.open("1,1,")), "TFFx")), ww_reply(FWt.step(ww_state(FWt.open("0,")), "FFT")), ww_reply(FWt.step(ww_state(FWt.step(ww_state(FWt.open("1,1,")), "FTF")), "TFF")), ww_reply(FWt.step(ww_state(FWt.open("2,")), "TFF"))] == ["1,0,", "1,2,", "1,1,", "0,", SCon{'E', SCon{' ', "wait: malformed poll"}}, SCon{'E', SCon{' ', "wait: malformed poll"}}, "0,", "0,", SCon{'E', SCon{' ', "wait: the open was refused"}}] : List<&2, String>}

# (D4) The walk the poll laws read, pinned
# ----------------------------------------
# The stepper runs the model's walk `Wt.go`; the laws above pin `Wt.run`.
# A fresh adversary filled `go` to hold a fired cancel until the next
# tick (poll `FTF` answered `0,`): `go` is pinned here against a walk
# written from D4 and H6.1.

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

# LAW wait_go_exact (R1): the model's walk is the first-end walk of D4: from any state, over any signals, it
# reports exactly the first end (the event, the cancel, the tick that passes the deadline) and
# nothing after it, and nothing from an ended wait
# EXCLUDES: a fired cancel or a ready event held for later, an end reported twice, an end after
#   the wait ended, a deadline passed a tick late or early
law wait_go_exact:
  for +xs: List<&2, Wt.Sig>
  for +w: Wt.W
  {Wt.go(xs, w) == go_spec(xs, w) : List<&2, Wt.End>}

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

def once_spec(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def reached_spec(dl: Maybe<&2, Nat>, k: Nat) -> Bool:
  match dl:
    case None{}:
      False{}
    case Some{d}:
      Nat.is_le(d, k)

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

# LAW wait_ends_once: a wait ends exactly once when its event, its cancel or its
# deadline comes, and never otherwise
law wait_ends_once_orig:
  for +dl: Maybe<&2, Nat>
  for +xs: List<&2, Wt.Sig>
  {List.length(&2, Wt.End, Wt.run(dl, xs)) == Wt.once(Wt.exits(dl, xs)) : Nat}

# LAW wait_end_is_final: once the cancel or the deadline came, the wait's end is final:
# what comes after changes nothing
law wait_end_is_final_orig:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Sig>
  for +post: List<&2, Wt.Sig>
  for stop: {Wt.stops(dl, pre) == True{} : Bool}
  {Wt.run(dl, List.append(&2, Wt.Sig, pre, post)) == Wt.run(dl, pre) : List<&2, Wt.End>}

# LAW wait_arrival_wins: an event that comes before the cancel and the deadline ends the
# wait with the event
law wait_arrival_wins_orig:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Sig>
  for +post: List<&2, Wt.Sig>
  for calm: {Wt.exits(dl, pre) == False{} : Bool}
  {Wt.run(dl, List.append(&2, Wt.Sig, pre, Wt.Arrive{} <> post)) == [Wt.Arrived{}] : List<&2, Wt.End>}

# LAW wait_cancel_wins: a cancel that comes before the event and the deadline ends the
# wait as cancelled
law wait_cancel_wins_orig:
  for +dl: Maybe<&2, Nat>
  for +pre: List<&2, Wt.Sig>
  for +post: List<&2, Wt.Sig>
  for calm: {Wt.exits(dl, pre) == False{} : Bool}
  {Wt.run(dl, List.append(&2, Wt.Sig, pre, Wt.Cancel{} <> post)) == [Wt.Cancelled{}] : List<&2, Wt.End>}
