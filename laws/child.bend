# eukhe: the laws of area child

import Base
import ../bend/child.bend as Ch
import ../bend/ffi_child.bend as FCh
import ./base.bend as LawsBase
import ../bend/wire.bend as Wr

# (H5) Every subagent reports back exactly once
# ---------------------------------------------
# bend/child.bend: the parent's task on one child. The watch's clock
# counts down the ms of no progress left (`left`, full: subagentStallMs)
# and the failed polls in a row left (`tries`, full: CHILD_POLL_FAILURES).

# LAW child_stalls_in_time: quiet polls (the child unsettled with the token the watch holds,
# or a failed poll), at least as many as the ms left on the clock, end the
# watch: each poll takes 1 ms or more
law child_stalls_in_time:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +h: Ch.Hush
  for +hs: List<&2, Ch.Hush>
  for long: {Nat.is_le(Ch.W.left(w), List.length(&2, Ch.Hush, h <> hs)) == True{} : Bool}
  {Ch.Next.watching(Ch.hush(h <> hs, cfg, Ch.Watch{w})) == False{} : Bool}

# LAW child_unreachable_in_time: failed polls in a row, as many as the tries left, end the watch
law child_unreachable_in_time:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +d: Nat
  for +ds: List<&2, Nat>
  for long: {Nat.is_le(Ch.W.tries(w), List.length(&2, Nat, d <> ds)) == True{} : Bool}
  {Ch.Next.watching(Ch.hush(Ch.misses(d <> ds), cfg, Ch.Watch{w})) == False{} : Bool}

# LAW child_clock_bounded: whatever a poll reads, the clock stays at most full: the bounds
# above are at most subagentStallMs and CHILD_POLL_FAILURES polls
law child_clock_bounded:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +o: Ch.Obs
  for full: {Ch.within(cfg, Ch.Watch{w}) == True{} : Bool}
  {Ch.within(cfg, Ch.look(cfg, w, e, o)) == True{} : Bool}

# LAW child_progress_is_not_a_stall: a poll that reads a new token (progress) is never a stall: the
# watch goes on with a full clock
law child_progress_is_not_a_stall:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +x: Nat
  for news: {Ch.moved(Ch.W.tok(w), Some{x}) == True{} : Bool}
  {Ch.look(cfg, w, e, Ch.Busy{Some{x}}) == Ch.Watch{Ch.W.fresh(cfg, Some{x})} : Ch.Next}

# The report laws hold after any events: task steps (polls), the parent's
# deliveries and withdrawals of any submission id, its aborts, closes and
# reopens, and task aborts and deletes, in any order. The parent's inbox
# keeps every submission of the report, each queued, withdrawn or placed.

# LAW child_one_live: at most one submission of the report is live (queued or placed):
# the task submits again only once its last submission is withdrawn, so
# no two ids of the report can both reach the transcript
law child_one_live:
  for +cfg: Ch.Cfg
  for +evs: List<&2, Ch.Ev>
  {Nat.is_le(Ch.live(Ch.St.inbox(Ch.run(evs, cfg, Ch.St.init(cfg)))), 1n) == True{} : Bool}

# LAW child_report_once: at most one submission of the report is placed: the parent's
# transcript holds the report at most once
law child_report_once:
  for +cfg: Ch.Cfg
  for +evs: List<&2, Ch.Ev>
  {Nat.is_le(Ch.St.placed(Ch.run(evs, cfg, Ch.St.init(cfg))), 1n) == True{} : Bool}

# LAW child_resubmits_per_abort: the report is submitted at most once more than the parent withdrew
# (an abort, a close, a withdrawal of one input): a resubmission follows a
# withdrawal
law child_resubmits_per_abort:
  for +cfg: Ch.Cfg
  for +evs: List<&2, Ch.Ev>
  {Nat.is_le(List.length(&2, Ch.Sub, Ch.St.inbox(Ch.run(evs, cfg, Ch.St.init(cfg)))), Nat.add(Ch.cuts(evs), 1n)) == True{} : Bool}

# LAW child_delivered_once: a report the task owes is placed exactly once when the parent
# reopens, the task takes three steps (the first may run a pending abort)
# and the parent's run places the submission the task then waits on (its
# owed id m): the report is never lost
law child_delivered_once:
  for +cfg: Ch.Cfg
  for +evs: List<&2, Ch.Ev>
  for +d1: Nat
  for +o1: Ch.Obs
  for +d2: Nat
  for +o2: Ch.Obs
  for +d3: Nat
  for +o3: Ch.Obs
  for owing: {Ch.Ph.owing(Ch.St.ph(Ch.run(evs, cfg, Ch.St.init(cfg)))) == True{} : Bool}
  for +m: Nat
  for waits: {Ch.St.owed(Ch.run([Ch.Reopen{}, Ch.Poll{d1, o1}, Ch.Poll{d2, o2}, Ch.Poll{d3, o3}], cfg, Ch.run(evs, cfg, Ch.St.init(cfg)))) == m : Nat}
  {Ch.St.placed(Ch.run([Ch.Reopen{}, Ch.Poll{d1, o1}, Ch.Poll{d2, o2}, Ch.Poll{d3, o3}, Ch.Deliver{m}], cfg, Ch.run(evs, cfg, Ch.St.init(cfg)))) == 1n : Nat}

# The task's decisions, as the Rust task runs them (bend/child.bend
# `verdict`, `owe.next`, `cut.ph`): the call on one poll, the report
# phase's move, the abort.

# the call a task in mode m makes on the watch's verdict x: watch on,
# report to the parent's inbox, or (a silent task, or a child that
# replied) end with no report, keeping why
def ChildActed(x: Ch.Next, m: Ch.Mode) -> Ch.Call:
  match x:
    case Ch.Watch{w}:
      Ch.Watches{w}
    case Ch.Owe{k}:
      match m:
        case Ch.Inbox{}:
          Ch.Reports{k}
        case Ch.Silent{}:
          Ch.Settles{Some{k}}
    case Ch.Quiet{}:
      Ch.Settles{None{}}

# the report phase's move on the fate of submission n: none yet, submit
# it under n; queued, wait; withdrawn, owe it under n + 1; placed, end
def ChildMove(f: Maybe<&2, Ch.Fate>, +n: Nat) -> Ch.Move:
  match f:
    case None{}:
      Ch.Submit{n}
    case Some{x}:
      match x:
        case Ch.Queued{}:
          Ch.Await{}
        case Ch.Withdrawn{}:
          Ch.Resubmit{1n+n}
        case Ch.Placed{}:
          Ch.Delivered{}

# the phase an abort leaves: a delete of a watched child owes a cancelled
# report under the first id, a cancel owes nothing, an owed report goes
# on as it was, an ended task stays ended
def ChildAbort(ph: Ch.Ph, del: Bool) -> Ch.Ph:
  match ph:
    case Ch.Watching{w}:
      match del:
        case True{}:
          Ch.Owing{Ch.Cancelled{}, 1n}
        case False{}:
          Ch.Ended{}
    case Ch.Owing{k, n}:
      Ch.Owing{k, n}
    case Ch.Ended{}:
      Ch.Ended{}

# LAW child_task_call: the task's call on a poll is the watch's verdict (`look`, which
# the laws above bound) as the task's mode acts on it
# EXCLUDES: a call that drops or invents a report, a silent task that
# reports, an inbox task that settles a child that owes a report
law child_task_call:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for o: Ch.Obs
  for m: Ch.Mode
  {Ch.verdict(cfg, w, e, o, m) == ChildActed(Ch.look(cfg, w, e, o), m) : Ch.Call}

# LAW child_silent_never_reports: a silent task never reports to its parent
law child_silent_never_reports:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for o: Ch.Obs
  {Ch.Call.reports(Ch.verdict(cfg, w, e, o, Ch.Silent{})) == False{} : Bool}

# LAW child_report_move: the report phase's move is the one report rule
# EXCLUDES: a second submission while one is queued, a resubmission under
# the same id, an end before the report is placed
law child_report_move:
  for f: Maybe<&2, Ch.Fate>
  for +n: Nat
  {Ch.owe.next(f, n) == ChildMove(f, n) : Ch.Move}

# LAW child_report_move_is_owe: the move, carried out, is the model's report rule `owe`, so the
# report laws above hold for the task the Rust code runs
law child_report_move_is_owe:
  for f: Maybe<&2, Ch.Fate>
  for k: Ch.Report
  for +n: Nat
  for open: Bool
  for inbox: List<&2, Ch.Sub>
  {Ch.owe.do(Ch.owe.next(f, n), k, n, open, inbox) == Ch.owe(f, k, n, open, inbox) : Ch.St}

# LAW child_abort_rule: the abort's rule
# EXCLUDES: a delete with no report, a cancel that reports, an abort that
# loses or restarts an owed report
law child_abort_rule:
  for ph: Ch.Ph
  for del: Bool
  {Ch.cut.ph(ph, del) == ChildAbort(ph, del) : Ch.Ph}

# ---- core_w6 ----

# LAWS: the entries of the compiled Bend core for the child task, the jobs,
# the goal's progress check and the hand-back (bend/ffi_child.bend,
# bend/ffi_job.bend, bend/ffi_progress.bend, bend/ffi_sandbox.bend). Each
# entry, on the request Rust writes (`put_req`, every number within the
# wire), answers the encoding of the model's decision: the codec loses,
# invents and reorders nothing, and the Rust rule is the proven model.

def wire_cfg_fits(c: Ch.Cfg) -> Bool:
  match c:
    case Ch.Cfg{s, f}:
      Bool.and(LawsBase.wire_fits(s), LawsBase.wire_fits(f))

def wire_w_fits(w: Ch.W) -> Bool:
  match w:
    case Ch.W{t, l, n}:
      Bool.and(LawsBase.wire_mfits(t), Bool.and(LawsBase.wire_fits(l), LawsBase.wire_fits(n)))

def wire_obs_fits(o: Ch.Obs) -> Bool:
  match o:
    case Ch.Busy{t}:
      LawsBase.wire_mfits(t)
    case Ch.Lost{}:
      True{}
    case Ch.Answered{r}:
      True{}
    case Ch.Broke{}:
      True{}
    case Ch.Gone{}:
      True{}

def wire_ph_fits(p: Ch.Ph) -> Bool:
  match p:
    case Ch.Watching{w}:
      wire_w_fits(w)
    case Ch.Owing{k, n}:
      LawsBase.wire_fits(n)
    case Ch.Ended{}:
      True{}

# LAW child_entry_verdict: the child entry's verdict request answers the task's call
# EXCLUDES: a codec that drops or swaps a field, a default for a field
law child_entry_verdict:
  for +c: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +o: Ch.Obs
  for +m: Ch.Mode
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for hw: {wire_w_fits(w) == True{} : Bool}
  for he: {LawsBase.wire_fits(e) == True{} : Bool}
  for ho: {wire_obs_fits(o) == True{} : Bool}
  {FCh.ffi(FCh.put_req(FCh.AskVerdict{c, w, e, o, m})) == FCh.put_call(Ch.verdict(c, w, e, o, m), "") : String}

# LAW child_entry_move: the child entry's move request answers the report phase's move
law child_entry_move:
  for +f: Maybe<&2, Ch.Fate>
  for +n: Nat
  for hn: {LawsBase.wire_fits(n) == True{} : Bool}
  {FCh.ffi(FCh.put_req(FCh.AskMove{f, n})) == FCh.put_move(Ch.owe.next(f, n), "") : String}

# LAW child_entry_abort: the child entry's abort request answers the abort's phase
law child_entry_abort:
  for +p: Ch.Ph
  for +d: Bool
  for hp: {wire_ph_fits(p) == True{} : Bool}
  {FCh.ffi(FCh.put_req(FCh.AskAbort{p, d})) == FCh.put_ph(Ch.cut.ph(p, d), "") : String}

# The child entry's wire, spelled from the wire primitives only (never the
# entry's own put_*): the grammar of bend/ffi_child.bend's header. A
# constructor is Wr.put_nat(<its tag>, <its fields>); a record is its
# fields in order; a Maybe is tag 0 (None) or tag 1 then the value.

# a Maybe<Nat>: 0 none, 1 then the Nat
def ch_spell_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_nat(x, rest))

# the watch's clock: the token, left, tries
def ch_spell_w(w: Ch.W, rest: String) -> String:
  match w:
    case Ch.W{t, l, n}:
      ch_spell_mnat(t, Wr.put_nat(l, Wr.put_nat(n, rest)))

# the settings: stall, fails
def ch_spell_cfg(c: Ch.Cfg, rest: String) -> String:
  match c:
    case Ch.Cfg{s, f}:
      Wr.put_nat(s, Wr.put_nat(f, rest))

# a poll: Busy 0 (token), Lost 1, Answered 2 (Bool), Broke 3, Gone 4
def ch_spell_obs(o: Ch.Obs, rest: String) -> String:
  match o:
    case Ch.Busy{t}:
      Wr.put_nat(0n, ch_spell_mnat(t, rest))
    case Ch.Lost{}:
      Wr.put_nat(1n, rest)
    case Ch.Answered{r}:
      Wr.put_nat(2n, Wr.put_bool(r, rest))
    case Ch.Broke{}:
      Wr.put_nat(3n, rest)
    case Ch.Gone{}:
      Wr.put_nat(4n, rest)

# a mode: Inbox 0, Silent 1
def ch_spell_mode(m: Ch.Mode, rest: String) -> String:
  match m:
    case Ch.Inbox{}:
      Wr.put_nat(0n, rest)
    case Ch.Silent{}:
      Wr.put_nat(1n, rest)

# a report: Completed 0, Failed 1, Cancelled 2, Stalled 3, Unreachable 4
def ch_spell_report(k: Ch.Report, rest: String) -> String:
  match k:
    case Ch.Completed{}:
      Wr.put_nat(0n, rest)
    case Ch.Failed{}:
      Wr.put_nat(1n, rest)
    case Ch.Cancelled{}:
      Wr.put_nat(2n, rest)
    case Ch.Stalled{}:
      Wr.put_nat(3n, rest)
    case Ch.Unreachable{}:
      Wr.put_nat(4n, rest)

# a Maybe<Report>: 0 none, 1 then the report
def ch_spell_mreport(m: Maybe<&2, Ch.Report>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{k}:
      Wr.put_nat(1n, ch_spell_report(k, rest))

# a call: Watches 0 (clock), Reports 1 (report), Settles 2 (Maybe<Report>)
def ch_spell_call(c: Ch.Call, rest: String) -> String:
  match c:
    case Ch.Watches{w}:
      Wr.put_nat(0n, ch_spell_w(w, rest))
    case Ch.Reports{k}:
      Wr.put_nat(1n, ch_spell_report(k, rest))
    case Ch.Settles{why}:
      Wr.put_nat(2n, ch_spell_mreport(why, rest))

# a fate: Queued 0, Withdrawn 1, Placed 2
def ch_spell_fate(f: Ch.Fate, rest: String) -> String:
  match f:
    case Ch.Queued{}:
      Wr.put_nat(0n, rest)
    case Ch.Withdrawn{}:
      Wr.put_nat(1n, rest)
    case Ch.Placed{}:
      Wr.put_nat(2n, rest)

# a Maybe<Fate>: 0 none, 1 then the fate
def ch_spell_mfate(f: Maybe<&2, Ch.Fate>, rest: String) -> String:
  match f:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, ch_spell_fate(x, rest))

# a move: Submit 0 (id), Await 1, Resubmit 2 (id), Delivered 3
def ch_spell_move(m: Ch.Move, rest: String) -> String:
  match m:
    case Ch.Submit{n}:
      Wr.put_nat(0n, Wr.put_nat(n, rest))
    case Ch.Await{}:
      Wr.put_nat(1n, rest)
    case Ch.Resubmit{n}:
      Wr.put_nat(2n, Wr.put_nat(n, rest))
    case Ch.Delivered{}:
      Wr.put_nat(3n, rest)

# a phase: Watching 0 (clock), Owing 1 (report, id), Ended 2
def ch_spell_ph(p: Ch.Ph, rest: String) -> String:
  match p:
    case Ch.Watching{w}:
      Wr.put_nat(0n, ch_spell_w(w, rest))
    case Ch.Owing{k, n}:
      Wr.put_nat(1n, ch_spell_report(k, Wr.put_nat(n, rest)))
    case Ch.Ended{}:
      Wr.put_nat(2n, rest)

# a request: 0 verdict (settings, clock, elapsed ms, poll, mode), 1 move
# (fate, id), 2 abort (phase, delete flag), then rest
def ch_spell_req(r: FCh.Req, rest: String) -> String:
  match r:
    case FCh.AskVerdict{c, w, e, o, m}:
      Wr.put_nat(0n, ch_spell_cfg(c, ch_spell_w(w, Wr.put_nat(e, ch_spell_obs(o, ch_spell_mode(m, rest))))))
    case FCh.AskMove{f, n}:
      Wr.put_nat(1n, ch_spell_mfate(f, Wr.put_nat(n, rest)))
    case FCh.AskAbort{p, d}:
      Wr.put_nat(2n, ch_spell_ph(p, Wr.put_bool(d, rest)))

# every number of a request fits the wire
def ch_req_fits(r: FCh.Req) -> Bool:
  match r:
    case FCh.AskVerdict{c, w, e, o, m}:
      Bool.and(wire_cfg_fits(c), Bool.and(wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), wire_obs_fits(o))))
    case FCh.AskMove{f, n}:
      LawsBase.wire_fits(n)
    case FCh.AskAbort{p, d}:
      wire_ph_fits(p)

# the spelled reply of the model's decision on request r
def ch_spell_answer(r: FCh.Req) -> String:
  match r:
    case FCh.AskVerdict{+c, +w, +e, o, m}:
      ch_spell_call(Ch.verdict(c, w, e, o, m), "")
    case FCh.AskMove{f, +n}:
      ch_spell_move(Ch.owe.next(f, n), "")
    case FCh.AskAbort{p, d}:
      ch_spell_ph(Ch.cut.ph(p, d), "")

# LAW child_entry_answers_spelled: a request spelled by the grammar, every
# number within the wire, is answered with the grammar's spelling of the
# model's decision (the call, the move, the phase)
# EXCLUDES: a request or reply tag that drifts from the grammar Rust reads
#   and writes (a swapped or renumbered tag on either side), a field lost,
#   swapped or defaulted, a reply spelled another way
law child_entry_answers_spelled:
  for +r: FCh.Req
  for fits: {ch_req_fits(r) == True{} : Bool}
  {FCh.ffi(ch_spell_req(r, "")) == ch_spell_answer(r) : String}

# LAW child_entry_left_over: a spelled request that fits, followed by any
# more input, answers the error form "child: input left over"
# EXCLUDES: trailing input ignored, or read as part of the request
law child_entry_left_over:
  for +r: FCh.Req
  for fits: {ch_req_fits(r) == True{} : Bool}
  for +c: Char
  for +t: String
  {FCh.ffi(ch_spell_req(r, SCon{c, t})) == Wr.err("child: input left over") : String}

# LAW child_entry_unknown_request: a request tag of 3 or more (within the
# wire) answers the error form "child: unknown request", whatever follows
# EXCLUDES: an unknown request read as a known one, or as another error
law child_entry_unknown_request:
  for +n: Nat
  for +rest: String
  for fit: {LawsBase.wire_fits(3n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(3n+n, rest)) == Wr.err("child: unknown request") : String}

# LAW child_entry_reads_only_requests: an answer that is not the error
# form answers a request: the input is exactly the spelling of a request
# whose numbers fit the wire, and the answer is the spelled reply of the
# model's decision on it
# EXCLUDES: a decoder that accepts an unknown tag (a poll, mode, fate,
#   report, phase or request tag), a missing or extra field, or input left
#   over, and answers it anyway (a default instead of the error form)
law child_entry_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FCh.ffi(s)) == False{} : Bool}
  exs r: FCh.Req
  {(s, (ch_req_fits(r), FCh.ffi(s))) == (ch_spell_req(r, ""), (True{}, ch_spell_answer(r))) : String & (Bool & String)}

# LAW child_entry_tags_example: anchor: the bytes Rust sends and reads for
# a verdict (a lost poll on a clock with one try left: report
# unreachable), a move (no fate yet: submit under 1) and an abort (an
# owed cancelled report goes on); an unknown poll tag (5) and an unknown
# request tag (3) are refused with their exact error bytes
# EXCLUDES: a tag table both sides of the Bend entry agree on but Rust
#   does not, an unknown tag read as a known one
law child_entry_tags_example:
  {[FCh.ffi("0,5,2,0,5,1,1,1,0,"), FCh.ffi("1,0,1,"), FCh.ffi("2,1,2,1,F"), FCh.ffi("0,5,2,0,5,1,1,5,0,"), FCh.ffi("3,")] == ["1,4,", "0,1,", "1,2,1,", "E child: bad poll", "E child: unknown request"] : List<&2, String>}

# a is one of the child entry's error replies: the error form of one of the
# texts bend/ffi_child.bend writes
def ch_named_error(+a: String) -> Bool:
  Bool.or(String.eq(a, Wr.err("child: bad request")), Bool.or(String.eq(a, Wr.err("child: unknown request")), Bool.or(String.eq(a, Wr.err("child: bad settings")), Bool.or(String.eq(a, Wr.err("child: bad clock")), Bool.or(String.eq(a, Wr.err("child: bad elapsed ms")), Bool.or(String.eq(a, Wr.err("child: bad poll")), Bool.or(String.eq(a, Wr.err("child: bad mode")), Bool.or(String.eq(a, Wr.err("child: input left over")), Bool.or(String.eq(a, Wr.err("child: bad fate")), Bool.or(String.eq(a, Wr.err("child: bad id")), Bool.or(String.eq(a, Wr.err("child: bad phase")), String.eq(a, Wr.err("child: bad delete flag")))))))))))))

# LAW child_entry_errors_named: every answer of the entry that is the error
# form is one of its named errors ("child: " then the request, unknown
# request, settings, clock, elapsed ms, poll, mode, input left over, fate,
# id, phase or delete flag); which input gets which is pinned below
# EXCLUDES: an error text Rust's caller does not know (an unprefixed or
#   reworded text), an error with no text
law child_entry_errors_named:
  for +s: String
  for err: {LawsBase.wire_opens_err(FCh.ffi(s)) == True{} : Bool}
  {ch_named_error(FCh.ffi(s)) == True{} : Bool}

# LAW child_entry_unknown_token: in a verdict request, a clock token tag
# past 1 (none, some) answers "child: bad clock", whatever follows
# EXCLUDES: an unknown token tag read as none or some, or named as another
#   field
law child_entry_unknown_token:
  for +c: Ch.Cfg
  for +n: Nat
  for +rest: String
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for fit: {LawsBase.wire_fits(2n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(0n, ch_spell_cfg(c, Wr.put_nat(2n+n, rest)))) == Wr.err("child: bad clock") : String}

# LAW child_entry_unknown_poll: in a verdict request, a poll tag past 4
# answers "child: bad poll", whatever follows
# EXCLUDES: an unknown poll read as a known one (the old TBad-as-Lost
#   mutant), or named as another field
law child_entry_unknown_poll:
  for +c: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +n: Nat
  for +rest: String
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for hw: {wire_w_fits(w) == True{} : Bool}
  for he: {LawsBase.wire_fits(e) == True{} : Bool}
  for fit: {LawsBase.wire_fits(5n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(0n, ch_spell_cfg(c, ch_spell_w(w, Wr.put_nat(e, Wr.put_nat(5n+n, rest)))))) == Wr.err("child: bad poll") : String}

# LAW child_entry_unknown_mode: in a verdict request, a mode tag past 1
# (inbox, silent) answers "child: bad mode", whatever follows
# EXCLUDES: an unknown mode read as inbox or silent, or named as another
#   field
law child_entry_unknown_mode:
  for +c: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for +o: Ch.Obs
  for +n: Nat
  for +rest: String
  for hc: {wire_cfg_fits(c) == True{} : Bool}
  for hw: {wire_w_fits(w) == True{} : Bool}
  for he: {LawsBase.wire_fits(e) == True{} : Bool}
  for ho: {wire_obs_fits(o) == True{} : Bool}
  for fit: {LawsBase.wire_fits(2n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(0n, ch_spell_cfg(c, ch_spell_w(w, Wr.put_nat(e, ch_spell_obs(o, Wr.put_nat(2n+n, rest))))))) == Wr.err("child: bad mode") : String}

# LAW child_entry_unknown_mfate: in a move request, a fate presence tag
# past 1 (none, some) answers "child: bad fate", whatever follows
# EXCLUDES: an unknown presence tag read as none or some
law child_entry_unknown_mfate:
  for +n: Nat
  for +rest: String
  for fit: {LawsBase.wire_fits(2n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(1n, Wr.put_nat(2n+n, rest))) == Wr.err("child: bad fate") : String}

# LAW child_entry_unknown_fate: in a move request, a fate tag past 2
# (queued, withdrawn, placed) answers "child: bad fate", whatever follows
# EXCLUDES: an unknown fate read as a known one
law child_entry_unknown_fate:
  for +n: Nat
  for +rest: String
  for fit: {LawsBase.wire_fits(3n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(1n, Wr.put_nat(1n, Wr.put_nat(3n+n, rest)))) == Wr.err("child: bad fate") : String}

# LAW child_entry_unknown_phase: in an abort request, a phase tag past 2
# (watching, owing, ended) answers "child: bad phase", whatever follows
# EXCLUDES: an unknown phase read as a known one
law child_entry_unknown_phase:
  for +n: Nat
  for +rest: String
  for fit: {LawsBase.wire_fits(3n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(2n, Wr.put_nat(3n+n, rest))) == Wr.err("child: bad phase") : String}

# LAW child_entry_unknown_report: in an abort request, an owing phase's
# report tag past 4 answers "child: bad phase", whatever follows
# EXCLUDES: an unknown report read as a known one
law child_entry_unknown_report:
  for +n: Nat
  for +rest: String
  for fit: {LawsBase.wire_fits(5n+n) == True{} : Bool}
  {FCh.ffi(Wr.put_nat(2n, Wr.put_nat(1n, Wr.put_nat(5n+n, rest)))) == Wr.err("child: bad phase") : String}

# LAW child_entry_errors_example: anchor: each field cut short names
# itself: no request, then the settings, clock, elapsed ms, poll and mode
# of a verdict, the fate and id of a move, the phase and delete flag of an
# abort
# EXCLUDES: two error texts swapped, a field's error named as another
law child_entry_errors_example:
  {[FCh.ffi(""), FCh.ffi("0,"), FCh.ffi("0,5,2,"), FCh.ffi("0,5,2,0,5,1,"), FCh.ffi("0,5,2,0,5,1,1,"), FCh.ffi("0,5,2,0,5,1,1,1,"), FCh.ffi("1,"), FCh.ffi("1,0,"), FCh.ffi("2,"), FCh.ffi("2,2,")] == [Wr.err("child: bad request"), Wr.err("child: bad settings"), Wr.err("child: bad clock"), Wr.err("child: bad elapsed ms"), Wr.err("child: bad poll"), Wr.err("child: bad mode"), Wr.err("child: bad fate"), Wr.err("child: bad id"), Wr.err("child: bad phase"), Wr.err("child: bad delete flag")] : List<&2, String>}
