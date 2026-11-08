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

# The orphan event machine's state, by its history

# a run: a run start opens it, a run end closes it, any other event keeps it
def orphan_run_ev(open: Bool, e: Or.Ev) -> Bool:
  match e:
    case Or.RunStart{}:
      True{}
    case Or.RunEnd{}:
      False{}
    case Or.Queue{}:
      open
    case Or.Drain{}:
      open
    case Or.CompactStart{}:
      open
    case Or.CompactEnd{}:
      open
    case Or.Gone{g}:
      open
    case Or.Back{}:
      open

def orphan_run_fold(evs: List<&2, Or.Ev>, open: Bool) -> Bool:
  match evs:
    case Nil{}:
      open
    case e <> rest:
      orphan_run_fold(rest, orphan_run_ev(open, e))

# whether a run is open after the history evs, from `open` (a left fold)
def orphan_run_open(open: Bool, evs: List<&2, Or.Ev>) -> Bool:
  orphan_run_fold(evs, open)

# a compaction: a compaction start opens it, a compaction end closes it,
# any other event keeps it
def orphan_compact_ev(open: Bool, e: Or.Ev) -> Bool:
  match e:
    case Or.RunStart{}:
      open
    case Or.RunEnd{}:
      open
    case Or.Queue{}:
      open
    case Or.Drain{}:
      open
    case Or.CompactStart{}:
      True{}
    case Or.CompactEnd{}:
      False{}
    case Or.Gone{g}:
      open
    case Or.Back{}:
      open

def orphan_compact_fold(evs: List<&2, Or.Ev>, open: Bool) -> Bool:
  match evs:
    case Nil{}:
      open
    case e <> rest:
      orphan_compact_fold(rest, orphan_compact_ev(open, e))

# whether a compaction is open after the history evs, from `open`
def orphan_compact_open(open: Bool, evs: List<&2, Or.Ev>) -> Bool:
  orphan_compact_fold(evs, open)

# the queued inputs: a queue adds one, a drain takes one (none stay none),
# any other event keeps them
def orphan_queued_ev(q: Nat, e: Or.Ev) -> Nat:
  match e:
    case Or.RunStart{}:
      q
    case Or.RunEnd{}:
      q
    case Or.Queue{}:
      1n+q
    case Or.Drain{}:
      Nat.sub(q, 1n)
    case Or.CompactStart{}:
      q
    case Or.CompactEnd{}:
      q
    case Or.Gone{g}:
      q
    case Or.Back{}:
      q

def orphan_queued_fold(evs: List<&2, Or.Ev>, q: Nat) -> Nat:
  match evs:
    case Nil{}:
      q
    case e <> rest:
      orphan_queued_fold(rest, orphan_queued_ev(q, e))

# the inputs queued after the history evs, from q
def orphan_queued(q: Nat, evs: List<&2, Or.Ev>) -> Nat:
  orphan_queued_fold(evs, q)

# the ms absent: the supervisor's g more ms add g, its answer resets them
# to 0, any other event keeps them
def orphan_absent_ev(a: Nat, e: Or.Ev) -> Nat:
  match e:
    case Or.RunStart{}:
      a
    case Or.RunEnd{}:
      a
    case Or.Queue{}:
      a
    case Or.Drain{}:
      a
    case Or.CompactStart{}:
      a
    case Or.CompactEnd{}:
      a
    case Or.Gone{g}:
      Nat.add(g, a)
    case Or.Back{}:
      0n

def orphan_absent_fold(evs: List<&2, Or.Ev>, a: Nat) -> Nat:
  match evs:
    case Nil{}:
      a
    case e <> rest:
      orphan_absent_fold(rest, orphan_absent_ev(a, e))

# the ms absent after the history evs, from a
def orphan_absent(a: Nat, evs: List<&2, Or.Ev>) -> Nat:
  orphan_absent_fold(evs, a)

# the live state a history means, from a fresh worker (no run, nothing
# queued, no compaction, 0 ms absent)
def orphan_state(+evs: List<&2, Or.Ev>) -> Or.W:
  Or.W{orphan_run_open(False{}, evs), orphan_queued(0n, evs), orphan_compact_open(False{}, evs), orphan_absent(0n, evs)}

# whether the worker holds work after the history: a run open, a
# compaction open, or an input queued
def orphan_busy(+evs: List<&2, Or.Ev>) -> Bool:
  Bool.or(orphan_run_open(False{}, evs), Bool.or(orphan_compact_open(False{}, evs), Nat.is_lt(0n, orphan_queued(0n, evs))))

# the exit is due after `absent` ms: without work once the window passed,
# with work once two windows passed
def orphan_due_by(+window: Nat, busy: Bool, +absent: Nat) -> Bool:
  match busy:
    case False{}:
      Nat.is_le(window, absent)
    case True{}:
      Nat.is_le(Nat.add(window, window), absent)

# whether the exit check after the history's last event is due, by the Nat
# arithmetic above on every non-empty history (no event, no exit check yet:
# the empty history is False)
def orphan_due(+window: Nat, evs: List<&2, Or.Ev>) -> Bool:
  match evs:
    case Nil{}:
      False{}
    case +e <> +rest:
      orphan_due_by(window, orphan_busy(e <> rest), orphan_absent(0n, e <> rest))

def orphan_work_of(busy: Bool) -> Or.Work:
  match busy:
    case False{}:
      Or.Idle{}
    case True{}:
      Or.Ongoing{}

# due: the exit with the work held (closes the session without work, hands
# it over busy with work, aborts nothing); not due: the worker lives on in w
def orphan_after_by(due: Bool, +busy: Bool, w: Or.W) -> Or.St:
  match due:
    case True{}:
      Or.Exited{Or.Out{orphan_exit_spec(orphan_work_of(busy)), orphan_work_of(busy), busy, False{}}}
    case False{}:
      Or.Live{w}

# what the worker is after the history evs, when it was live before its
# last event
def orphan_after(+window: Nat, +evs: List<&2, Or.Ev>) -> Or.St:
  orphan_after_by(orphan_due(window, evs), orphan_busy(evs), orphan_state(evs))

# LAW orphan_live_state: a live worker's state is what its history says: a run is open
# exactly when a run start came after the last run end, a compaction
# likewise, the inputs queued are the queues less the drains (a drain of
# none takes nothing), the ms absent are the sum of the absences since
# the supervisor last answered (any window, any history)
# EXCLUDES: a run or compaction its end does not close (or another event
# opens or closes), a lost, invented or underflowed queued input, a lost
# or ignored absence, an absence kept past the supervisor's answer
law orphan_live_state:
  for +window: Nat
  for +evs: List<&2, Or.Ev>
  for +w: Or.W
  for live: {Or.run(window, evs) == Or.Live{w} : Or.St}
  {w == orphan_state(evs) : Or.W}

# LAW orphan_live_not_due: a live worker never skipped a due exit: the exit check after its
# last event was not due (the empty history is unchecked: no event, no exit
# check yet)
# EXCLUDES: a worker kept alive past its window (or two windows with
# work), an exit check skipped or computed on a wrong work or absence
law orphan_live_not_due:
  for +window: Nat
  for +evs: List<&2, Or.Ev>
  for +w: Or.W
  for live: {Or.run(window, evs) == Or.Live{w} : Or.St}
  {orphan_due(window, evs) == False{} : Bool}

# LAW orphan_next_by_history: one more event after a live history: when the exit is due on the
# longer history the worker exits, closing the session without work and
# handing it over busy with work, aborting nothing; else it lives on with
# the state of the longer history
# EXCLUDES: an early or missed exit, an exit with the wrong work, way,
# busy flag or abort, a wrong next state
law orphan_next_by_history:
  for +window: Nat
  for +evs: List<&2, Or.Ev>
  for +e: Or.Ev
  for +w: Or.W
  for live: {Or.run(window, evs) == Or.Live{w} : Or.St}
  {Or.run(window, List.append(&2, Or.Ev, evs, [e])) == orphan_after(window, List.append(&2, Or.Ev, evs, [e])) : Or.St}

# LAW orphan_exited_stays: an exited worker stays exited with the same outcome, whatever the
# next event
# EXCLUDES: a worker that revives, or changes its recorded exit, after it
# exited
law orphan_exited_stays:
  for +window: Nat
  for +evs: List<&2, Or.Ev>
  for +e: Or.Ev
  for +d: Or.Out
  for out: {Or.run(window, evs) == Or.Exited{d} : Or.St}
  {Or.run(window, List.append(&2, Or.Ev, evs, [e])) == Or.Exited{d} : Or.St}

# LAW orphan_starts_live: before any event a worker lives with no run, nothing queued, no
# compaction and no absence, for every window (the exit check runs only
# after an event)
# EXCLUDES: a worker that starts exited (or with made-up work or absence),
#   which makes every law on a live worker vacuous and quits before its
#   window passed
law orphan_starts_live:
  for +window: Nat
  {Or.run(window, Nil{}) == Or.Live{orphan_state(Nil{})} : Or.St}

# LAW orphan_history_example: anchor and witnesses, window 2: a compaction that ended, then
# 2 ms absent, exits shut idle; a compaction still open after 2 ms stays
# live compacting; after 4 ms it exits handing over busy; a run open
# after a compaction ended stays live with the run open; two queues and a
# drain keep one input queued
# EXCLUDES: vacuous premises of the laws above, a machine wrong on these
# histories
law orphan_history_example:
  {[Or.run(2n, [Or.CompactStart{}, Or.CompactEnd{}, Or.Gone{2n}]), Or.run(2n, [Or.CompactStart{}, Or.Gone{2n}]), Or.run(2n, [Or.CompactStart{}, Or.Gone{4n}]), Or.run(2n, [Or.RunStart{}, Or.CompactStart{}, Or.CompactEnd{}]), Or.run(2n, [Or.Queue{}, Or.Queue{}, Or.Drain{}])] == [Or.Exited{Or.Out{Or.Shut{}, Or.Idle{}, False{}, False{}}}, Or.Live{Or.W{False{}, 0n, True{}, 2n}}, Or.Exited{Or.Out{Or.Handover{}, Or.Ongoing{}, True{}, False{}}}, Or.Live{Or.W{True{}, 0n, False{}, 0n}}, Or.Live{Or.W{False{}, 1n, False{}, 0n}}] : List<&2, Or.St>}

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

# The orphan entry, spelled by the grammar Rust writes and reads
# (crates/eukhe-daemon/src/work_gate.rs `orphan_call`), not by the entry's
# own encoders

# a window: 0 none (past the wire's range), 1 then the window in ms
def orphan_spell_mwindow(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

# the work: Idle 0, Ongoing 1
def orphan_spell_work(k: Or.Work, rest: String) -> String:
  match k:
    case Or.Idle{}:
      Wr.put_nat(0n, rest)
    case Or.Ongoing{}:
      Wr.put_nat(1n, rest)

# the exit: Shut 0, Handover 1
def orphan_spell_exit(e: Or.Exit, rest: String) -> String:
  match e:
    case Or.Shut{}:
      Wr.put_nat(0n, rest)
    case Or.Handover{}:
      Wr.put_nat(1n, rest)

# a request: the window, the ms absent, the work, then rest
def orphan_spell_req(q: FO.Req, rest: String) -> String:
  match q:
    case FO.Req{m, a, k}:
      orphan_spell_mwindow(m, Wr.put_nat(a, orphan_spell_work(k, rest)))

# every number of a request fits the wire
def orphan_req_fits(q: FO.Req) -> Bool:
  match q:
    case FO.Req{m, a, k}:
      Bool.and(LawsBase.wire_mfits(m), LawsBase.wire_fits(a))

# whether the worker exits now: no window never; without work once the
# window passed; with work once two windows passed
def orphan_due_spec(m: Maybe<&2, Nat>, +a: Nat, k: Or.Work) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{+w}:
      match k:
        case Or.Idle{}:
          Nat.is_le(w, a)
        case Or.Ongoing{}:
          Nat.is_le(Nat.add(w, w), a)

# the spelled reply of the spec's decision on request q: due, then the exit
def orphan_spell_answer(q: FO.Req) -> String:
  match q:
    case FO.Req{m, +a, +k}:
      Wr.put_bool(orphan_due_spec(m, a, k), orphan_spell_exit(orphan_exit_spec(k), ""))

# LAW orphan_ffi_answers_spelled: a request spelled by the grammar, every number within the
# wire, is answered with the grammar's spelling of the decision: T when the
# exit is due (no window: never; no work: once the window passed; work:
# once two windows passed), else F, then the exit tag (0 shut without
# work, 1 handover with work)
# EXCLUDES: a due flag written reversed, an exit, work or window tag that
#   drifts from the grammar Rust reads and writes (swapped on both sides of
#   the entry alike), a field lost, swapped or defaulted
law orphan_ffi_answers_spelled:
  for +q: FO.Req
  for fits: {orphan_req_fits(q) == True{} : Bool}
  {FO.ffi(orphan_spell_req(q, "")) == orphan_spell_answer(q) : String}

# LAW orphan_ffi_left_over_spelled: a spelled request that fits, followed by any more input,
# answers the error form "orphan: input left over"
# EXCLUDES: trailing input ignored, or read as part of the request
law orphan_ffi_left_over_spelled:
  for +q: FO.Req
  for fits: {orphan_req_fits(q) == True{} : Bool}
  for +c: Char
  for +t: String
  {FO.ffi(orphan_spell_req(q, SCon{c, t})) == Wr.err("orphan: input left over") : String}

# LAW orphan_ffi_unknown_work: a spelled window and absence that fit, then a work tag of 2 or
# more (of any length), answer the error form "orphan: malformed request",
# whatever follows
# EXCLUDES: an unknown work tag read as a known work, or as another error
law orphan_ffi_unknown_work:
  for +m: Maybe<&2, Nat>
  for +a: Nat
  for fits: {Bool.and(LawsBase.wire_mfits(m), LawsBase.wire_fits(a)) == True{} : Bool}
  for +n: Nat
  for +rest: String
  {FO.ffi(orphan_spell_mwindow(m, Wr.put_nat(a, Wr.put_nat(2n+n, rest)))) == Wr.err("orphan: malformed request") : String}

# LAW orphan_ffi_unknown_window: a window tag of 2 or more (of any length) answers the error
# form "orphan: malformed request", whatever follows
# EXCLUDES: an unknown window tag read as none or some window
law orphan_ffi_unknown_window:
  for +n: Nat
  for +rest: String
  {FO.ffi(Wr.put_nat(2n+n, rest)) == Wr.err("orphan: malformed request") : String}

# LAW orphan_ffi_reads_only_requests: an answer that is not the error form answers a request:
# the input is exactly the spelling of a request whose numbers fit the
# wire, and the answer is the spelled reply of the spec's decision on it
# EXCLUDES: a decoder that accepts an unknown tag (window or work), a
#   missing or extra field, or input left over, and answers it anyway (a
#   default instead of the error form)
law orphan_ffi_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FO.ffi(s)) == False{} : Bool}
  exs q: FO.Req
  {(s, (orphan_req_fits(q), FO.ffi(s))) == (orphan_spell_req(q, ""), (True{}, orphan_spell_answer(q))) : String & (Bool & String)}

# LAW orphan_ffi_malformed_unless_request: every answer but the error form "orphan: malformed
# request" comes from an input that begins with a spelled request that fits
# EXCLUDES: the left-over error (or any answer) for input that does not
#   begin with a request, the malformed error spelled with another text
law orphan_ffi_malformed_unless_request:
  for +s: String
  for other: {String.eq(FO.ffi(s), Wr.err("orphan: malformed request")) == False{} : Bool}
  exs q: FO.Req
  exs rest: String
  {(s, orphan_req_fits(q)) == (orphan_spell_req(q, rest), True{}) : String & Bool}

# LAW orphan_ffi_tags_example: anchor: the bytes Rust sends and reads: window 2, 5 ms absent,
# no work: due, shut (T0,); 1 ms absent: not due (F0,); work, 4 ms: due,
# handover (T1,); work, 3 ms: not due, handover (F1,); no window, 9 ms:
# never due (F0,); work tag 2 and window tag 2 are malformed; a request
# with input left over is refused
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust
#   does not, a reversed due flag, an unknown tag read as a known one
law orphan_ffi_tags_example:
  {[FO.ffi("1,2,5,0,"), FO.ffi("1,2,1,0,"), FO.ffi("1,2,4,1,"), FO.ffi("1,2,3,1,"), FO.ffi("0,9,0,"), FO.ffi("1,2,5,2,"), FO.ffi("2,5,0,"), FO.ffi("1,2,5,0,x")] == ["T0,", "F0,", "T1,", "F1,", "F0,", Wr.err("orphan: malformed request"), Wr.err("orphan: malformed request"), Wr.err("orphan: input left over")] : List<&2, String>}


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
# The exit's soundness, as a Bool
# -------------------------------
# orphan_never_aborts_resumable states the model predicate Or.Sound: a
# Sound rewritten to `Unit` makes it vacuous. It is pinned here, both
# ways, to a Bool in the laws.

def ongoing_spec(work: Or.Work) -> Bool:
  match work:
    case Or.Idle{}:
      False{}
    case Or.Ongoing{}:
      True{}

# a is b
def same_bool_spec(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

# a live worker is sound; an exit is sound when it aborted nothing and
# recorded the session busy exactly when it held work
def sound_spec(s: Or.St) -> Bool:
  match s:
    case Or.Live{w}:
      True{}
    case Or.Exited{d}:
      match d:
        case Or.Out{e, work, busy, aborted}:
          Bool.and(Bool.not(aborted), same_bool_spec(busy, ongoing_spec(work)))

# LAW orphan_sound_iff: the model's soundness predicate holds exactly when its Bool in the laws is true: a live worker always; an exit exactly when it aborted nothing and recorded the session busy exactly when it held work
# EXCLUDES: an Or.Sound rewritten to `Unit` (or one that ignores the abort or the busy flag), which makes orphan_never_aborts_resumable vacuous
law orphan_sound_iff:
  for +s: Or.St
  (Or.Sound(s) -> {sound_spec(s) == True{} : Bool}) & ({sound_spec(s) == True{} : Bool} -> Or.Sound(s))
