# eukhe: the laws of area orphan

import Base
import ../bend/ffi_orphan.bend as FO
import ../bend/orphan.bend as Or
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# The restart-budget entry of the compiled core (bend/ffi_supervise.bend)

# LAW orphan_never_aborts_resumable: a lost supervisor's worker never aborts work a later supervisor can
# resume: its exit aborts nothing and records the session busy exactly
# when it held work
law orphan_never_aborts_resumable:
  for +window: Nat
  for +evs: List<&2, Or.Ev>
  Or.Sound(Or.run(window, evs))

# LAW orphan_idle_exit_due: an orphaned worker without work exits once the whole window passed
# (any window, any absence)
# EXCLUDES: an exit before the window, a worker kept alive past it
law orphan_idle_exit_due:
  for +window: Nat
  for +absent: Nat
  {Or.exit_due.at(Some{window}, absent, Or.Idle{}) == Nat.is_le(window, absent) : Bool}

# LAW orphan_work_exit_due: an orphaned worker with work exits once two windows passed: the
# work defers the exit by exactly one more window, never forever
# EXCLUDES: work that does not defer the exit, defers it forever, or by
# a wrong amount
law orphan_work_exit_due:
  for +window: Nat
  for +absent: Nat
  {Or.exit_due.at(Some{window}, absent, Or.Ongoing{}) == Nat.is_le(Nat.add(window, window), absent) : Bool}

# LAW orphan_capped_window_never_expires: a window past the runtime's Nat range (Rust saturates a larger env
# window to `None`) never expires, whatever the absence and the work
# EXCLUDES: a saturated huge window that turns into an early exit
law orphan_capped_window_never_expires:
  for +absent: Nat
  for work: Or.Work
  {Or.exit_due.at(None{}, absent, work) == False{} : Bool}

def orphan_exit_spec(work: Or.Work) -> Or.Exit:
  match work:
    case Or.Idle{}:
      Or.Shut{}
    case Or.Ongoing{}:
      Or.Handover{}

# LAW orphan_exit_by_work: without work the orphan exit closes the session; with work it
# hands the work over (both values of Work)
# EXCLUDES: a handover of nothing, a close that drops work
law orphan_exit_by_work:
  for work: Or.Work
  {Or.orphan_exit(work) == orphan_exit_spec(work) : Or.Exit}

# The orphan entry of the compiled core (bend/ffi_orphan.bend)

# LAW orphan_wire_req_window: the entry reads back every request Rust writes: a window that fits
# the wire, an absence that fits, the work; the rest is untouched
# EXCLUDES: a misread window, absence or work, a lost or eaten rest
law orphan_wire_req_window:
  for +w: Nat
  for hw: {LawsBase.wire_fits(w) == True{} : Bool}
  for +a: Nat
  for ha: {LawsBase.wire_fits(a) == True{} : Bool}
  for +k: Or.Work
  for rest: String
  {FO.get_req(FO.put_req(FO.Req{Some{w}, a, k}, rest)) == Wr.Got{FO.Req{Some{w}, a, k}, rest} : Wr.Dec<FO.Req>}

# LAW orphan_wire_req_no_window: and a request with no window (past the wire's range)
# EXCLUDES: a missing window read as some window
law orphan_wire_req_no_window:
  for +a: Nat
  for ha: {LawsBase.wire_fits(a) == True{} : Bool}
  for +k: Or.Work
  for rest: String
  {FO.get_req(FO.put_req(FO.Req{None{}, a, k}, rest)) == Wr.Got{FO.Req{None{}, a, k}, rest} : Wr.Dec<FO.Req>}

# LAW orphan_wire_reply: Rust reads back every reply the entry writes
# EXCLUDES: a swapped due flag or exit
law orphan_wire_reply:
  for +d: Bool
  for +e: Or.Exit
  for rest: String
  {FO.get_reply(FO.put_reply(FO.Reply{d, e}, rest)) == Wr.Got{FO.Reply{d, e}, rest} : Wr.Dec<FO.Reply>}

# LAW orphan_ffi_decides: on a whole request the entry answers the model's decision: whether
# the worker exits now, and how
# EXCLUDES: an entry that answers anything but exit_due.at and orphan_exit
law orphan_ffi_decides:
  for +s: String
  for +m: Maybe<&2, Nat>
  for +a: Nat
  for +k: Or.Work
  for h: {FO.get_req(s) == Wr.Got{FO.Req{m, a, k}, ""} : Wr.Dec<FO.Req>}
  {FO.ffi(s) == FO.put_reply(FO.Reply{Or.exit_due.at(m, a, k), Or.orphan_exit(k)}, "") : String}

# LAW orphan_ffi_malformed: a malformed request answers the error form, never a decision
# EXCLUDES: a default decision on garbage
law orphan_ffi_malformed:
  for +s: String
  for h: {FO.get_req(s) == Wr.Bad{} : Wr.Dec<FO.Req>}
  {FO.ffi(s) == Wr.err("orphan: malformed request") : String}

# LAW orphan_ffi_left_over: a request with input after it answers the error form
# EXCLUDES: a decision on a request with trailing garbage
law orphan_ffi_left_over:
  for +s: String
  for +q: FO.Req
  for +r: String
  for h: {FO.get_req(s) == Wr.Got{q, r} : Wr.Dec<FO.Req>}
  for ne: {String.is_empty(r) == False{} : Bool}
  {FO.ffi(s) == Wr.err("orphan: input left over") : String}

# The whole entry, every input
# ----------------------------
# The request and the reply as the wire grammar of WIRE.md, read and
# spelled with the wire primitives alone (never the entry's own codec),
# and the decision as the requirement states it (never the model's code):
#   request  the window: 0 (none, past the wire's range) | 1 then the
#            window; the absence; the work: 0 idle | 1 ongoing
#   reply    whether the worker exits now, then how: 0 shut | 1 handover
# A request that cannot be read answers "orphan: malformed request"; a
# request with input after it answers "orphan: input left over".

def or_read.work(m: Maybe<&2, Nat>, a: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<FO.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{FO.Req{m, a, Or.Idle{}}, s}
        case 1n:
          Wr.Got{FO.Req{m, a, Or.Ongoing{}}, s}
        case 2n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def or_read.absent(m: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<FO.Req>:
  match r:
    case Wr.Got{a, s}:
      or_read.work(m, a, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def or_read.window(r: Wr.Dec<Nat>) -> Wr.Dec<FO.Req>:
  match r:
    case Wr.Got{w, s}:
      or_read.absent(Some{w}, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def or_read.tag(r: Wr.Dec<Nat>) -> Wr.Dec<FO.Req>:
  match r:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          or_read.absent(None{}, Wr.get_nat(s))
        case 1n:
          or_read.window(Wr.get_nat(s))
        case 2n+p:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# the request at the head of s, and the input after it
def or_read(s: String) -> Wr.Dec<FO.Req>:
  or_read.tag(Wr.get_nat(s))

# the worker exits now: never with no window (past the wire's range);
# without work once the window passed; with work once two windows passed
def or_due(m: Maybe<&2, Nat>, +a: Nat, k: Or.Work) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+w}:
      match k:
        case Or.Idle{}:
          Nat.is_le(w, a)
        case Or.Ongoing{}:
          Nat.is_le(Nat.add(w, w), a)

# how the worker exits: without work it shuts the session (0), with work
# it hands the work over (1)
def or_exit_tag(k: Or.Work) -> Nat:
  match k:
    case Or.Idle{}:
      0n
    case Or.Ongoing{}:
      1n

def or_reply(q: FO.Req) -> String:
  match q:
    case FO.Req{m, a, +k}:
      Wr.put_bool(or_due(m, a, k), Wr.put_nat(or_exit_tag(k), ""))

def or_entry.of(d: Wr.Dec<FO.Req>) -> String:
  match d:
    case Wr.Got{q, r}:
      match r:
        case SNil{}:
          or_reply(q)
        case SCon{c, t}:
          Wr.err("orphan: input left over")
    case Wr.Bad{}:
      Wr.err("orphan: malformed request")

# the entry's answer to s
def or_entry(s: String) -> String:
  or_entry.of(or_read(s))

# LAW orphan_ffi_exact: for every input, the entry answers exactly: on a request (as the wire
# primitives read it) with nothing after it, whether the worker exits now
# (never with no window; idle once the window passed; with work once two
# windows passed) and how (idle: shut, with work: handover); on a request
# with input after it, the error form "orphan: input left over"; on any
# other input, the error form "orphan: malformed request"
# EXCLUDES: a misread or reordered field, a tag read as another, an exit
#   before or after its window, a swapped exit, a decision on garbage or on
#   a request with input after it, another error text, a codec of the
#   entry wrong both ways (the spec never calls it)
law orphan_ffi_exact:
  for +s: String
  {FO.ffi(s) == or_entry(s) : String}

# LAW orphan_ffi_exact_example: anchor: the strings Rust writes and the replies it reads: an
# idle worker past its window, a working one inside its second window, no
# window; an unknown window tag and input left over are refused
# EXCLUDES: a field order other than Rust's, a vacuous orphan_ffi_exact
law orphan_ffi_exact_example:
  {[or_entry("1,5,5,0,"), or_entry("1,5,9,1,"), or_entry("0,7,1,"), or_entry("2,5,0,"), or_entry("1,5,5,0,x")] == ["T0,", "F1,", "F1,", Wr.err("orphan: malformed request"), Wr.err("orphan: input left over")] : List<&2, String>}

# The event machine, whole
# -------------------------
# bend/orphan.bend's `step` and `run` (the history of
# orphan_never_aborts_resumable), spelled as the header states them with
# the decision `or_due` of the entry's spec (never the model's code):
# a worker holds work when a run, a compaction or a queued input is
# there; each event moves one field (a drain stops at zero, an absence
# adds up, the supervisor's return zeroes it); after each event the
# worker exits when or_due says so, without work closing the session
# (idle, nothing aborted), with work handing it over (busy, nothing
# aborted); an exited worker stays exited.

# the work of a worker: ongoing when it runs, compacts, or holds a queued
# input; idle otherwise
def ow_work(w: Or.W) -> Or.Work:
  match w:
    case Or.W{r, q, c, a}:
      match r:
        case True{}:
          Or.Ongoing{}
        case False{}:
          match q:
            case 0n:
              match c:
                case True{}:
                  Or.Ongoing{}
                case False{}:
                  Or.Idle{}
            case 1n+p:
              Or.Ongoing{}

# a drain takes one queued input, none from an empty queue
def ow_drain(q: Nat) -> Nat:
  match q:
    case 0n:
      0n
    case 1n+p:
      p

# the worker after one event
def ow_apply(w: Or.W, e: Or.Ev) -> Or.W:
  match w:
    case Or.W{r, q, c, a}:
      match e:
        case Or.RunStart{}:
          Or.W{True{}, q, c, a}
        case Or.RunEnd{}:
          Or.W{False{}, q, c, a}
        case Or.Queue{}:
          Or.W{r, 1n+q, c, a}
        case Or.Drain{}:
          Or.W{r, ow_drain(q), c, a}
        case Or.CompactStart{}:
          Or.W{r, q, True{}, a}
        case Or.CompactEnd{}:
          Or.W{r, q, False{}, a}
        case Or.Gone{g}:
          Or.W{r, q, c, Nat.add(g, a)}
        case Or.Back{}:
          Or.W{r, q, c, 0n}

# what the exit records: without work it shuts the session, records it
# idle, aborts nothing; with work it hands the work over, records the
# session busy, aborts nothing
def ow_out(k: Or.Work) -> Or.Out:
  match k:
    case Or.Idle{}:
      Or.Out{Or.Shut{}, Or.Idle{}, False{}, False{}}
    case Or.Ongoing{}:
      Or.Out{Or.Handover{}, Or.Ongoing{}, True{}, False{}}

def ow_check.put(due: Bool, +w: Or.W) -> Or.St:
  match due:
    case True{}:
      Or.Exited{ow_out(ow_work(w))}
    case False{}:
      Or.Live{w}

# the exit check after an event: the worker exits when or_due says so
# for its window, its absence and its work
def ow_check(+window: Nat, +w: Or.W) -> Or.St:
  match w:
    case Or.W{r, q, c, +a}:
      ow_check.put(or_due(Some{window}, a, ow_work(Or.W{r, q, c, a})), Or.W{r, q, c, a})

# one event: a live worker moves and checks the exit; an exited one stays
def ow_step(+window: Nat, s: Or.St, e: Or.Ev) -> Or.St:
  match s:
    case Or.Live{w}:
      ow_check(window, ow_apply(w, e))
    case Or.Exited{d}:
      Or.Exited{d}

def ow_go(+window: Nat, evs: List<&2, Or.Ev>, s: Or.St) -> Or.St:
  match evs:
    case Nil{}:
      s
    case e <> rest:
      ow_go(window, rest, ow_step(window, s, e))

# the events from a fresh worker: no run, no queued input, no
# compaction, no absence
def ow_run(+window: Nat, evs: List<&2, Or.Ev>) -> Or.St:
  ow_go(window, evs, Or.Live{Or.W{False{}, 0n, False{}, 0n}})

# LAW orphan_work_spec (D1): every worker holds work exactly when it runs,
# compacts, or holds a queued input
# EXCLUDES: a W.work that answers Idle always (the audit's rewrite: the
#   exit then shuts and aborts nothing it should hand over, and
#   orphan_never_aborts_resumable still holds), one blind to a run, a
#   compaction or the queue, one that counts the absence as work
law orphan_work_spec:
  for +w: Or.W
  {Or.W.work(w) == ow_work(w) : Or.Work}

# LAW orphan_step_spec (D1): from every state, every event moves the
# worker and decides its exit exactly as the header states it
# EXCLUDES: an event applied to the wrong field or dropped, a drain below
#   zero that wraps, an absence that resets or does not add up, an exit
#   check skipped or run before the event, an exit on the wrong window, a
#   wrong exit record, an exited worker that comes back or changes its
#   record
law orphan_step_spec:
  for +window: Nat
  for +s: Or.St
  for +e: Or.Ev
  {Or.step(window, s, e) == ow_step(window, s, e) : Or.St}

# LAW orphan_run_spec (D1): for every window and every history of events,
# the worker ends in exactly the state the spec's fold reaches from a
# fresh worker
# EXCLUDES: a run from a worker that is not fresh, events folded in
#   another order or some skipped, a W.work that answers Idle always (an
#   idle exit for a worker that runs), any wrong step
law orphan_run_spec:
  for +window: Nat
  for +evs: List<&2, Or.Ev>
  {Or.run(window, evs) == ow_run(window, evs) : Or.St}
