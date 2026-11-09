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

# The orphan exit check and the work it records

# the exit is due after `absent` ms: without work once the window passed,
# with work once two windows passed
def orphan_due_by(+window: Nat, busy: Bool, +absent: Nat) -> Bool:
  match busy:
    case False{}:
      Nat.is_le(window, absent)
    case True{}:
      Nat.is_le(Nat.add(window, window), absent)

def orphan_work_of(busy: Bool) -> Or.Work:
  match busy:
    case False{}:
      Or.Idle{}
    case True{}:
      Or.Ongoing{}

# The worker's state, declared by what its history contains
# ---------------------------------------------------------
#
# No step-by-step state: each field is a property of the whole history,
# read over what comes after each event (docs/daemon.md D1: runs and
# compactions start and end, inputs are queued and drained, the supervisor
# stays away g more ms or answers).

# which events start and end a run, a compaction
def orphan_starts_run(e: Or.Ev) -> Bool:
  match e:
    case Or.RunStart{}:
      True{}
    case Or.RunEnd{}:
      False{}
    case Or.Queue{}:
      False{}
    case Or.Drain{}:
      False{}
    case Or.CompactStart{}:
      False{}
    case Or.CompactEnd{}:
      False{}
    case Or.Gone{g}:
      False{}
    case Or.Back{}:
      False{}

def orphan_ends_run(e: Or.Ev) -> Bool:
  match e:
    case Or.RunStart{}:
      False{}
    case Or.RunEnd{}:
      True{}
    case Or.Queue{}:
      False{}
    case Or.Drain{}:
      False{}
    case Or.CompactStart{}:
      False{}
    case Or.CompactEnd{}:
      False{}
    case Or.Gone{g}:
      False{}
    case Or.Back{}:
      False{}

def orphan_starts_compaction(e: Or.Ev) -> Bool:
  match e:
    case Or.RunStart{}:
      False{}
    case Or.RunEnd{}:
      False{}
    case Or.Queue{}:
      False{}
    case Or.Drain{}:
      False{}
    case Or.CompactStart{}:
      True{}
    case Or.CompactEnd{}:
      False{}
    case Or.Gone{g}:
      False{}
    case Or.Back{}:
      False{}

def orphan_ends_compaction(e: Or.Ev) -> Bool:
  match e:
    case Or.RunStart{}:
      False{}
    case Or.RunEnd{}:
      False{}
    case Or.Queue{}:
      False{}
    case Or.Drain{}:
      False{}
    case Or.CompactStart{}:
      False{}
    case Or.CompactEnd{}:
      True{}
    case Or.Gone{g}:
      False{}
    case Or.Back{}:
      False{}

# whether no event of the history ends a run
def orphan_no_run_end(evs: List<&2, Or.Ev>) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(Bool.not(orphan_ends_run(e)), orphan_no_run_end(rest))

# whether a run is open after the history: some run start of it has no
# run end after it
def orphan_run_unended(evs: List<&2, Or.Ev>) -> Bool:
  match evs:
    case Nil{}:
      False{}
    case e <> +rest:
      Bool.or(Bool.and(orphan_starts_run(e), orphan_no_run_end(rest)), orphan_run_unended(rest))

# whether no event of the history ends a compaction
def orphan_no_compaction_end(evs: List<&2, Or.Ev>) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(Bool.not(orphan_ends_compaction(e)), orphan_no_compaction_end(rest))

# whether a compaction is open after the history: some compaction start of
# it has no compaction end after it
def orphan_compaction_unended(evs: List<&2, Or.Ev>) -> Bool:
  match evs:
    case Nil{}:
      False{}
    case e <> +rest:
      Bool.or(Bool.and(orphan_starts_compaction(e), orphan_no_compaction_end(rest)), orphan_compaction_unended(rest))

# a queue counts 1, any other event 0
def orphan_one_queue(e: Or.Ev) -> Nat:
  match e:
    case Or.RunStart{}:
      0n
    case Or.RunEnd{}:
      0n
    case Or.Queue{}:
      1n
    case Or.Drain{}:
      0n
    case Or.CompactStart{}:
      0n
    case Or.CompactEnd{}:
      0n
    case Or.Gone{g}:
      0n
    case Or.Back{}:
      0n

# a drain counts 1, any other event 0
def orphan_one_drain(e: Or.Ev) -> Nat:
  match e:
    case Or.RunStart{}:
      0n
    case Or.RunEnd{}:
      0n
    case Or.Queue{}:
      0n
    case Or.Drain{}:
      1n
    case Or.CompactStart{}:
      0n
    case Or.CompactEnd{}:
      0n
    case Or.Gone{g}:
      0n
    case Or.Back{}:
      0n

# the queues of the history
def orphan_queues(evs: List<&2, Or.Ev>) -> Nat:
  match evs:
    case Nil{}:
      0n
    case e <> rest:
      Nat.add(orphan_one_queue(e), orphan_queues(rest))

# the drains of the history
def orphan_drains(evs: List<&2, Or.Ev>) -> Nat:
  match evs:
    case Nil{}:
      0n
    case e <> rest:
      Nat.add(orphan_one_drain(e), orphan_drains(rest))

# the inputs queued after the history: the most the queues outnumber the
# drains by in any final stretch of it (the empty stretch, and a stretch
# with more drains, count 0)
def orphan_queued_most(evs: List<&2, Or.Ev>) -> Nat:
  match evs:
    case Nil{}:
      0n
    case +e <> +rest:
      Nat.max(Nat.sub(orphan_queues(e <> rest), orphan_drains(e <> rest)), orphan_queued_most(rest))

# the ms of an absence, 0 for any other event
def orphan_gone_ms(e: Or.Ev) -> Nat:
  match e:
    case Or.RunStart{}:
      0n
    case Or.RunEnd{}:
      0n
    case Or.Queue{}:
      0n
    case Or.Drain{}:
      0n
    case Or.CompactStart{}:
      0n
    case Or.CompactEnd{}:
      0n
    case Or.Gone{g}:
      g
    case Or.Back{}:
      0n

# whether the event is the supervisor's answer
def orphan_answers(e: Or.Ev) -> Bool:
  match e:
    case Or.RunStart{}:
      False{}
    case Or.RunEnd{}:
      False{}
    case Or.Queue{}:
      False{}
    case Or.Drain{}:
      False{}
    case Or.CompactStart{}:
      False{}
    case Or.CompactEnd{}:
      False{}
    case Or.Gone{g}:
      False{}
    case Or.Back{}:
      True{}

# whether no event of the history is the supervisor's answer
def orphan_no_answer(evs: List<&2, Or.Ev>) -> Bool:
  match evs:
    case Nil{}:
      True{}
    case e <> rest:
      Bool.and(Bool.not(orphan_answers(e)), orphan_no_answer(rest))

# the ms absent after the history: the sum of the absences the supervisor
# did not answer after
def orphan_unanswered_ms(evs: List<&2, Or.Ev>) -> Nat:
  match evs:
    case Nil{}:
      0n
    case e <> +rest:
      Nat.add(Bool.pick(Nat, orphan_no_answer(rest), orphan_gone_ms(e), 0n), orphan_unanswered_ms(rest))

# the state the history declares
def orphan_declared(+evs: List<&2, Or.Ev>) -> Or.W:
  Or.W{orphan_run_unended(evs), orphan_queued_most(evs), orphan_compaction_unended(evs), orphan_unanswered_ms(evs)}

# whether the history declares work: a run open, a compaction open, or an
# input queued
def orphan_declared_busy(+evs: List<&2, Or.Ev>) -> Bool:
  Bool.or(orphan_run_unended(evs), Bool.or(orphan_compaction_unended(evs), Nat.is_lt(0n, orphan_queued_most(evs))))

# whether the worker exited
def orphan_exited(s: Or.St) -> Bool:
  match s:
    case Or.Live{w}:
      False{}
    case Or.Exited{d}:
      True{}

# LAW orphan_live_by_history: a live worker's state is what its history declares: a run is
# open exactly when some run start of the history has no run end after it,
# a compaction likewise; the inputs queued are the most the queues
# outnumber the drains by in any final stretch of the history (so a drain
# of none takes nothing, and no more stay queued than were queued); the ms
# absent are the sum of the absences the supervisor did not answer after
# (any window, any history)
# EXCLUDES: a run or compaction its end does not close (or another event
#   opens or closes), a lost, invented or underflowed queued input, a drain
#   of none kept as a debt against later queues, a lost or ignored
#   absence, an absence kept past the supervisor's answer
law orphan_live_by_history:
  for +window: Nat
  for +evs: List<&2, Or.Ev>
  for +w: Or.W
  for live: {Or.run(window, evs) == Or.Live{w} : Or.St}
  {w == orphan_declared(evs) : Or.W}

# LAW orphan_live_not_due: a live worker never skipped a due exit: after any history and one
# more event that leave the worker live, the exit is not due on what that
# history declares: without work (no run or compaction open, no input
# queued) its unanswered absence is below the window, with work below two
# windows (the empty history has no event and no exit check yet)
# EXCLUDES: a worker kept alive past its window (or two windows with
#   work), an exit check skipped or computed on a wrong work or absence
law orphan_live_not_due:
  for +window: Nat
  for +evs: List<&2, Or.Ev>
  for +e: Or.Ev
  for +w: Or.W
  for live: {Or.run(window, List.append(&2, Or.Ev, evs, [e])) == Or.Live{w} : Or.St}
  {orphan_due_by(window, orphan_declared_busy(List.append(&2, Or.Ev, evs, [e])), orphan_unanswered_ms(List.append(&2, Or.Ev, evs, [e]))) == False{} : Bool}

# LAW orphan_exits_when_due: one more event after a live history exits the worker exactly when
# the exit is due on the longer history, read from what that history
# declares: without work (no run or compaction open, no input queued) once
# its unanswered absence reaches the window, with work once it reaches two
# windows
# EXCLUDES: an early or missed exit, an exit check on a wrong work or
#   absence, a worker that exits on a not due check or lives past a due one
law orphan_exits_when_due:
  for +window: Nat
  for +evs: List<&2, Or.Ev>
  for +e: Or.Ev
  for +w: Or.W
  for live: {Or.run(window, evs) == Or.Live{w} : Or.St}
  {orphan_exited(Or.run(window, List.append(&2, Or.Ev, evs, [e]))) == orphan_due_by(window, orphan_declared_busy(List.append(&2, Or.Ev, evs, [e])), orphan_unanswered_ms(List.append(&2, Or.Ev, evs, [e]))) : Bool}

# LAW orphan_exit_holds_work: when one more event exits a live worker, the exit records the work
# the longer history declares: without work it closes the session idle,
# with work it hands it over and records the session busy; it aborts
# nothing either way
# EXCLUDES: an exit that drops, invents or misreports the work, a close of
#   a session with work, a handover of nothing, an abort
law orphan_exit_holds_work:
  for +window: Nat
  for +evs: List<&2, Or.Ev>
  for +e: Or.Ev
  for +w: Or.W
  for live: {Or.run(window, evs) == Or.Live{w} : Or.St}
  for +d: Or.Out
  for out: {Or.run(window, List.append(&2, Or.Ev, evs, [e])) == Or.Exited{d} : Or.St}
  {d == Or.Out{orphan_exit_spec(orphan_work_of(orphan_declared_busy(List.append(&2, Or.Ev, evs, [e])))), orphan_work_of(orphan_declared_busy(List.append(&2, Or.Ev, evs, [e]))), orphan_declared_busy(List.append(&2, Or.Ev, evs, [e])), False{}} : Or.Out}

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

# LAW orphan_starts_live: for every window, a worker that has seen no event is live with no run,
# nothing queued, no compaction and no absence (the laws over histories
# take a live state before their last event as a premise, so the start
# pins every history; a fresh blind adversary's worker that started
# exited for any window above 2 ms passed every other law)
# EXCLUDES: a worker that exits, or starts busy or absent, before any event
law orphan_starts_live:
  for +window: Nat
  {Or.run(window, Nil{}) == Or.Live{Or.W{False{}, 0n, False{}, 0n}} : Or.St}

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
