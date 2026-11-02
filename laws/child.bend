# eukhe: the laws of area child

import Base
import ../bend/child.bend as Ch
import ../bend/ffi_child.bend as FCh
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

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

# ---- the child entry: spelled requests (bend/ffi_child.bend, id 4) ----
#
# LAWS: the three decisions the Rust task asks of the compiled core (the
# watch's call on a poll, crates/eukhe-core/src/durable/children/watch.rs;
# the report phase's move and the abort, children/task.rs), on requests
# spelled from the primitives of bend/wire.bend (not the entry's own
# codecs), read by the laws' own reader, answered from the laws' own rules
# (ChildActed, ChildMove, ChildAbort above, and the watch's verdict below).
#
# K1: the watch's verdict on one poll that read o, e ms after the last:
#     a child that settled with a reply to its parent ends the watch with
#     no report, one that settled without one owes Completed, one that
#     failed or is gone owes Failed; an unsettled child whose token moved
#     (a token, and the watch held none or another) gets a full clock
#     (stall ms and tries from the settings) on that token; an unsettled
#     child with no progress keeps its token, has e ms fewer left (none
#     left: it owes Stalled) and its tries back to full; a failed poll with
#     one try left or none owes Unreachable, else it has e ms fewer left
#     (none left: Stalled) and one try fewer.
# K2: on every input that is exactly one request the entry answers the
#     decision spelled; on any other input exactly the error form naming
#     the first part that does not read ("child: bad request", "child:
#     unknown request", "child: bad settings", "child: bad clock", "child:
#     bad elapsed ms", "child: bad poll", "child: bad mode", "child: bad
#     fate", "child: bad id", "child: bad phase", "child: bad delete flag")
#     or, after a whole request, "child: input left over".

# The watch's verdict (K1)
# ------------------------

# progress: the poll read a token, and the watch held none or another
def ch_news(tok: Maybe<&2, Nat>, t: Maybe<&2, Nat>) -> Bool:
  match tok:
    case None{}:
      match t:
        case None{}:
          False{}
        case Some{x}:
          True{}
    case Some{y}:
      match t:
        case None{}:
          False{}
        case Some{x}:
          Bool.not(Nat.is_eq(y, x))

# a poll with no progress that leaves `rest` ms: none left is a stall,
# else the watch goes on with token tok and `tries` failed polls left
def ch_quiet(rest: Nat, tok: Maybe<&2, Nat>, tries: Nat) -> Ch.Next:
  match rest:
    case 0n:
      Ch.Owe{Ch.Stalled{}}
    case 1n+p:
      Ch.Watch{Ch.W{tok, 1n+p, tries}}

def ch_busy(news: Bool, cfg: Ch.Cfg, t: Maybe<&2, Nat>, tok: Maybe<&2, Nat>, left: Nat, e: Nat) -> Ch.Next:
  match news:
    case True{}:
      match cfg:
        case Ch.Cfg{s, f}:
          Ch.Watch{Ch.W{t, s, f}}
    case False{}:
      match cfg:
        case Ch.Cfg{s, f}:
          ch_quiet(Nat.sub(left, e), tok, f)

def ch_lost(tries: Nat, tok: Maybe<&2, Nat>, left: Nat, e: Nat) -> Ch.Next:
  match tries:
    case 0n:
      Ch.Owe{Ch.Unreachable{}}
    case 1n:
      Ch.Owe{Ch.Unreachable{}}
    case 2n+q:
      ch_quiet(Nat.sub(left, e), tok, 1n+q)

def ch_settled(replied: Bool) -> Ch.Next:
  match replied:
    case True{}:
      Ch.Quiet{}
    case False{}:
      Ch.Owe{Ch.Completed{}}

# the watch's verdict on one poll that read o, e ms after the last (K1)
def ch_look_spec(cfg: Ch.Cfg, w: Ch.W, e: Nat, o: Ch.Obs) -> Ch.Next:
  match w:
    case Ch.W{+tok, left, tries}:
      match o:
        case Ch.Busy{+t}:
          ch_busy(ch_news(tok, t), cfg, t, tok, left, e)
        case Ch.Lost{}:
          ch_lost(tries, tok, left, e)
        case Ch.Answered{r}:
          ch_settled(r)
        case Ch.Broke{}:
          Ch.Owe{Ch.Failed{}}
        case Ch.Gone{}:
          Ch.Owe{Ch.Failed{}}

# LAW child_look_exact (K1): the watch's verdict on one poll (which child_task_call and the clock laws read) is K1's verdict, for every setting, clock, elapsed ms and poll
# EXCLUDES: a stall before the clock runs out or after, a failed poll
#   that never ends the watch or ends it a try early, a successful poll
#   that keeps the failed polls counted, progress read from an unchanged
#   or absent token, a clock not refilled to the settings, a settled child
#   watched on or reported as another end
law child_look_exact:
  for +cfg: Ch.Cfg
  for +w: Ch.W
  for +e: Nat
  for o: Ch.Obs
  {Ch.look(cfg, w, e, o) == ch_look_spec(cfg, w, e, o) : Ch.Next}

# The wire (spellers over the primitives of bend/wire.bend)
# --------------------------------------------------------

# a Maybe Nat: 0 none | 1, then the Nat
def ch_spell_mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_nat(x, rest))

# the settings: stall ms, then tries
def ch_spell_cfg(c: Ch.Cfg, rest: String) -> String:
  match c:
    case Ch.Cfg{s, f}:
      Wr.put_nat(s, Wr.put_nat(f, rest))

# the clock: the token, the ms left, the tries left
def ch_spell_w(w: Ch.W, rest: String) -> String:
  match w:
    case Ch.W{t, l, n}:
      ch_spell_mnat(t, Wr.put_nat(l, Wr.put_nat(n, rest)))

# a poll: Busy 0 (the token) | Lost 1 | Answered 2 (T|F replied) | Broke 3 | Gone 4
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

# a mode: Inbox 0 | Silent 1
def ch_spell_mode(m: Ch.Mode, rest: String) -> String:
  match m:
    case Ch.Inbox{}:
      Wr.put_nat(0n, rest)
    case Ch.Silent{}:
      Wr.put_nat(1n, rest)

# a report: Completed 0 | Failed 1 | Cancelled 2 | Stalled 3 | Unreachable 4
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

# a submission's fate, if any: 0 none | 1, then Queued 0 | Withdrawn 1 | Placed 2
def ch_spell_mfate(f: Maybe<&2, Ch.Fate>, rest: String) -> String:
  match f:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      match x:
        case Ch.Queued{}:
          Wr.put_nat(1n, Wr.put_nat(0n, rest))
        case Ch.Withdrawn{}:
          Wr.put_nat(1n, Wr.put_nat(1n, rest))
        case Ch.Placed{}:
          Wr.put_nat(1n, Wr.put_nat(2n, rest))

# a phase: Watching 0 (the clock) | Owing 1 (the report, the id) | Ended 2
def ch_spell_ph(p: Ch.Ph, rest: String) -> String:
  match p:
    case Ch.Watching{w}:
      Wr.put_nat(0n, ch_spell_w(w, rest))
    case Ch.Owing{k, n}:
      Wr.put_nat(1n, ch_spell_report(k, Wr.put_nat(n, rest)))
    case Ch.Ended{}:
      Wr.put_nat(2n, rest)

# a request as Rust writes it: 0 the verdict (settings, clock, elapsed ms,
# poll, mode), 1 the move (fate, id), 2 the abort (phase, T|F delete)
def ch_spell_req(q: FCh.Req, rest: String) -> String:
  match q:
    case FCh.AskVerdict{c, w, e, o, m}:
      Wr.put_nat(0n, ch_spell_cfg(c, ch_spell_w(w, Wr.put_nat(e, ch_spell_obs(o, ch_spell_mode(m, rest))))))
    case FCh.AskMove{f, n}:
      Wr.put_nat(1n, ch_spell_mfate(f, Wr.put_nat(n, rest)))
    case FCh.AskAbort{p, d}:
      Wr.put_nat(2n, ch_spell_ph(p, Wr.put_bool(d, rest)))

# the task's call: Watches 0 (the clock) | Reports 1 (the report) |
# Settles 2 (0 no report | 1, then the report it does not send)
def ch_spell_call(c: Ch.Call) -> String:
  match c:
    case Ch.Watches{w}:
      Wr.put_nat(0n, ch_spell_w(w, ""))
    case Ch.Reports{k}:
      Wr.put_nat(1n, ch_spell_report(k, ""))
    case Ch.Settles{why}:
      match why:
        case None{}:
          Wr.put_nat(2n, Wr.put_nat(0n, ""))
        case Some{k}:
          Wr.put_nat(2n, Wr.put_nat(1n, ch_spell_report(k, "")))

# the move: Submit 0 (id) | Await 1 | Resubmit 2 (id) | Delivered 3
def ch_spell_move(m: Ch.Move) -> String:
  match m:
    case Ch.Submit{n}:
      Wr.put_nat(0n, Wr.put_nat(n, ""))
    case Ch.Await{}:
      Wr.put_nat(1n, "")
    case Ch.Resubmit{n}:
      Wr.put_nat(2n, Wr.put_nat(n, ""))
    case Ch.Delivered{}:
      Wr.put_nat(3n, "")

# the decision on a request, spelled (K1, ChildActed, ChildMove, ChildAbort)
def ch_answer(q: FCh.Req) -> String:
  match q:
    case FCh.AskVerdict{c, w, e, o, m}:
      ch_spell_call(ChildActed(ch_look_spec(c, w, e, o), m))
    case FCh.AskMove{f, +n}:
      ch_spell_move(ChildMove(f, n))
    case FCh.AskAbort{p, d}:
      ch_spell_ph(ChildAbort(p, d), "")

# every number of a request fits the wire
def ch_req_fits(q: FCh.Req) -> Bool:
  match q:
    case FCh.AskVerdict{c, w, e, o, m}:
      Bool.and(wire_cfg_fits(c), Bool.and(wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), wire_obs_fits(o))))
    case FCh.AskMove{f, n}:
      LawsBase.wire_fits(n)
    case FCh.AskAbort{p, d}:
      wire_ph_fits(p)

# the error form with text t
def ch_err(t: String) -> String:
  SCon{'E', SCon{' ', t}}

# The laws' reader (each part from the decode of the Nat that starts it)
# ----------------------------------------------------------------------

def ch_read_mnat.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Some{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_mnat.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      ch_read_mnat.some(Wr.get_nat(s))
    case 2n+q:
      Wr.Bad{}

def ch_read_mnat(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{t, s}:
      ch_read_mnat.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_cfg.f(+st: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Ch.Cfg>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{Ch.Cfg{st, f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_cfg(r: Wr.Dec<Nat>) -> Wr.Dec<Ch.Cfg>:
  match r:
    case Wr.Got{+st, s}:
      ch_read_cfg.f(st, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_w.n(t: Maybe<&2, Nat>, +l: Nat, r: Wr.Dec<Nat>) -> Wr.Dec<Ch.W>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Ch.W{t, l, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_w.l(t: Maybe<&2, Nat>, r: Wr.Dec<Nat>) -> Wr.Dec<Ch.W>:
  match r:
    case Wr.Got{+l, s}:
      ch_read_w.n(t, l, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_w(r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Ch.W>:
  match r:
    case Wr.Got{t, s}:
      ch_read_w.l(t, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_obs.busy(r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<Ch.Obs>:
  match r:
    case Wr.Got{t, s}:
      Wr.Got{Ch.Busy{t}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_obs.answered(r: Wr.Dec<Bool>) -> Wr.Dec<Ch.Obs>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{Ch.Answered{b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_obs.tag(t: Nat, s: String) -> Wr.Dec<Ch.Obs>:
  match t:
    case 0n:
      ch_read_obs.busy(ch_read_mnat(Wr.get_nat(s)))
    case 1n:
      Wr.Got{Ch.Lost{}, s}
    case 2n:
      ch_read_obs.answered(Wr.get_bool(s))
    case 3n:
      Wr.Got{Ch.Broke{}, s}
    case 4n:
      Wr.Got{Ch.Gone{}, s}
    case 5n+q:
      Wr.Bad{}

def ch_read_obs(r: Wr.Dec<Nat>) -> Wr.Dec<Ch.Obs>:
  match r:
    case Wr.Got{t, s}:
      ch_read_obs.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_mode.tag(t: Nat, s: String) -> Wr.Dec<Ch.Mode>:
  match t:
    case 0n:
      Wr.Got{Ch.Inbox{}, s}
    case 1n:
      Wr.Got{Ch.Silent{}, s}
    case 2n+q:
      Wr.Bad{}

def ch_read_mode(r: Wr.Dec<Nat>) -> Wr.Dec<Ch.Mode>:
  match r:
    case Wr.Got{t, s}:
      ch_read_mode.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_report.tag(t: Nat, s: String) -> Wr.Dec<Ch.Report>:
  match t:
    case 0n:
      Wr.Got{Ch.Completed{}, s}
    case 1n:
      Wr.Got{Ch.Failed{}, s}
    case 2n:
      Wr.Got{Ch.Cancelled{}, s}
    case 3n:
      Wr.Got{Ch.Stalled{}, s}
    case 4n:
      Wr.Got{Ch.Unreachable{}, s}
    case 5n+q:
      Wr.Bad{}

def ch_read_report(r: Wr.Dec<Nat>) -> Wr.Dec<Ch.Report>:
  match r:
    case Wr.Got{t, s}:
      ch_read_report.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_fate.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Ch.Fate>>:
  match t:
    case 0n:
      Wr.Got{Some{Ch.Queued{}}, s}
    case 1n:
      Wr.Got{Some{Ch.Withdrawn{}}, s}
    case 2n:
      Wr.Got{Some{Ch.Placed{}}, s}
    case 3n+q:
      Wr.Bad{}

def ch_read_fate(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Ch.Fate>>:
  match r:
    case Wr.Got{t, s}:
      ch_read_fate.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_mfate.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Ch.Fate>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      ch_read_fate(Wr.get_nat(s))
    case 2n+q:
      Wr.Bad{}

def ch_read_mfate(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Ch.Fate>>:
  match r:
    case Wr.Got{t, s}:
      ch_read_mfate.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_ph.watching(r: Wr.Dec<Ch.W>) -> Wr.Dec<Ch.Ph>:
  match r:
    case Wr.Got{w, s}:
      Wr.Got{Ch.Watching{w}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_ph.n(k: Ch.Report, r: Wr.Dec<Nat>) -> Wr.Dec<Ch.Ph>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Ch.Owing{k, n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_ph.owing(r: Wr.Dec<Ch.Report>) -> Wr.Dec<Ch.Ph>:
  match r:
    case Wr.Got{k, s}:
      ch_read_ph.n(k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def ch_read_ph.tag(t: Nat, s: String) -> Wr.Dec<Ch.Ph>:
  match t:
    case 0n:
      ch_read_ph.watching(ch_read_w(ch_read_mnat(Wr.get_nat(s))))
    case 1n:
      ch_read_ph.owing(ch_read_report(Wr.get_nat(s)))
    case 2n:
      Wr.Got{Ch.Ended{}, s}
    case 3n+q:
      Wr.Bad{}

def ch_read_ph(r: Wr.Dec<Nat>) -> Wr.Dec<Ch.Ph>:
  match r:
    case Wr.Got{t, s}:
      ch_read_ph.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

# The reply (K2)
# --------------

def ch_spec.verdict.fin(whole: Bool, +c: Ch.Cfg, +w: Ch.W, +e: Nat, o: Ch.Obs, m: Ch.Mode) -> String:
  match whole:
    case True{}:
      ch_spell_call(ChildActed(ch_look_spec(c, w, e, o), m))
    case False{}:
      ch_err("child: input left over")

def ch_spec.verdict.m(+c: Ch.Cfg, +w: Ch.W, +e: Nat, +o: Ch.Obs, r: Wr.Dec<Ch.Mode>) -> String:
  match r:
    case Wr.Got{m, s}:
      ch_spec.verdict.fin(Wr.end(s), c, w, e, o, m)
    case Wr.Bad{}:
      ch_err("child: bad mode")

def ch_spec.verdict.o(+c: Ch.Cfg, +w: Ch.W, +e: Nat, r: Wr.Dec<Ch.Obs>) -> String:
  match r:
    case Wr.Got{+o, s}:
      ch_spec.verdict.m(c, w, e, o, ch_read_mode(Wr.get_nat(s)))
    case Wr.Bad{}:
      ch_err("child: bad poll")

def ch_spec.verdict.e(+c: Ch.Cfg, +w: Ch.W, r: Wr.Dec<Nat>) -> String:
  match r:
    case Wr.Got{+e, s}:
      ch_spec.verdict.o(c, w, e, ch_read_obs(Wr.get_nat(s)))
    case Wr.Bad{}:
      ch_err("child: bad elapsed ms")

def ch_spec.verdict.w(+c: Ch.Cfg, r: Wr.Dec<Ch.W>) -> String:
  match r:
    case Wr.Got{+w, s}:
      ch_spec.verdict.e(c, w, Wr.get_nat(s))
    case Wr.Bad{}:
      ch_err("child: bad clock")

def ch_spec.verdict.c(r: Wr.Dec<Ch.Cfg>) -> String:
  match r:
    case Wr.Got{+c, s}:
      ch_spec.verdict.w(c, ch_read_w(ch_read_mnat(Wr.get_nat(s))))
    case Wr.Bad{}:
      ch_err("child: bad settings")

def ch_spec.move.fin(whole: Bool, f: Maybe<&2, Ch.Fate>, +n: Nat) -> String:
  match whole:
    case True{}:
      ch_spell_move(ChildMove(f, n))
    case False{}:
      ch_err("child: input left over")

def ch_spec.move.n(f: Maybe<&2, Ch.Fate>, r: Wr.Dec<Nat>) -> String:
  match r:
    case Wr.Got{+n, s}:
      ch_spec.move.fin(Wr.end(s), f, n)
    case Wr.Bad{}:
      ch_err("child: bad id")

def ch_spec.move.f(r: Wr.Dec<Maybe<&2, Ch.Fate>>) -> String:
  match r:
    case Wr.Got{f, s}:
      ch_spec.move.n(f, Wr.get_nat(s))
    case Wr.Bad{}:
      ch_err("child: bad fate")

def ch_spec.abort.fin(whole: Bool, p: Ch.Ph, d: Bool) -> String:
  match whole:
    case True{}:
      ch_spell_ph(ChildAbort(p, d), "")
    case False{}:
      ch_err("child: input left over")

def ch_spec.abort.d(p: Ch.Ph, r: Wr.Dec<Bool>) -> String:
  match r:
    case Wr.Got{d, s}:
      ch_spec.abort.fin(Wr.end(s), p, d)
    case Wr.Bad{}:
      ch_err("child: bad delete flag")

def ch_spec.abort.p(r: Wr.Dec<Ch.Ph>) -> String:
  match r:
    case Wr.Got{p, s}:
      ch_spec.abort.d(p, Wr.get_bool(s))
    case Wr.Bad{}:
      ch_err("child: bad phase")

def ch_spec.tag(t: Nat, s: String) -> String:
  match t:
    case 0n:
      ch_spec.verdict.c(ch_read_cfg(Wr.get_nat(s)))
    case 1n:
      ch_spec.move.f(ch_read_mfate(Wr.get_nat(s)))
    case 2n:
      ch_spec.abort.p(ch_read_ph(Wr.get_nat(s)))
    case 3n+q:
      ch_err("child: unknown request")

def ch_spec.go(r: Wr.Dec<Nat>) -> String:
  match r:
    case Wr.Got{t, s}:
      ch_spec.tag(t, s)
    case Wr.Bad{}:
      ch_err("child: bad request")

# the reply to s (K2): the decision on the request s is exactly, else the
# error form naming the first part that does not read
def ch_spec(s: String) -> String:
  ch_spec.go(Wr.get_nat(s))

# LAW child_ffi_exact (K2): on every input the child entry answers the decision on the request the input is exactly (the watch's call: K1's verdict as the task's mode acts on it; the report phase's move; the abort's phase), spelled; on any other input exactly the error form naming the first part that does not read, or the input left over
# EXCLUDES: a decision other than the rules' (a lost or invented report, a
#   stall early or late, a resubmission under the same id), a codec that
#   drops, swaps or misreads a field, a default for malformed input, an
#   unknown tag read as a known one, input left over ignored, another
#   error text
law child_ffi_exact:
  for +s: String
  {FCh.ffi(s) == ch_spec(s) : String}

# LAW child_ffi_answers (K2): every request Rust writes (every number within the wire) gets the decision on it
# EXCLUDES: a request Rust writes refused or misread
law child_ffi_answers:
  for +q: FCh.Req
  for fits: {ch_req_fits(q) == True{} : Bool}
  {FCh.ffi(ch_spell_req(q, "")) == ch_answer(q) : String}

# LAW child_ffi_example (K1, K2): anchor: the strings Rust sends and the replies: a poll with no progress (the tries back to full), progress, a stall, a failed poll on its last try, a reply, a broken child of a silent task; each move; each abort; and one malformed input per error text
# EXCLUDES: another spelling of a request or a reply
law child_ffi_example:
  {[FCh.ffi("0,100,3,1,7,50,2,10,0,1,7,0,"), FCh.ffi("0,100,3,1,7,50,2,10,0,1,8,0,"), FCh.ffi("0,100,3,1,7,50,2,50,0,1,7,0,"), FCh.ffi("0,100,3,1,7,50,1,10,1,0,"), FCh.ffi("0,100,3,0,50,3,10,2,T1,"), FCh.ffi("0,100,3,0,50,3,10,3,1,")] == ["0,1,7,40,3,", "0,1,8,100,3,", "1,3,", "1,4,", "2,0,", "2,1,1,"] : List<&2, String>} &
  {[FCh.ffi("1,0,4,"), FCh.ffi("1,1,0,4,"), FCh.ffi("1,1,1,4,"), FCh.ffi("1,1,2,4,"), FCh.ffi("2,0,1,7,50,3,T"), FCh.ffi("2,0,0,50,3,F"), FCh.ffi("2,1,3,4,T")] == ["0,4,", "1,", "2,5,", "3,", "1,2,1,", "2,", "1,3,4,"] : List<&2, String>} &
  {[FCh.ffi(""), FCh.ffi("3,"), FCh.ffi("0,x"), FCh.ffi("0,1,2,x"), FCh.ffi("0,1,2,0,5,5,x"), FCh.ffi("0,1,2,0,5,5,1,9,"), FCh.ffi("0,1,2,0,5,5,1,1,2,"), FCh.ffi("0,1,2,0,5,5,1,1,0,x")] == [ch_err("child: bad request"), ch_err("child: unknown request"), ch_err("child: bad settings"), ch_err("child: bad clock"), ch_err("child: bad elapsed ms"), ch_err("child: bad poll"), ch_err("child: bad mode"), ch_err("child: input left over")] : List<&2, String>} &
  {[FCh.ffi("1,2,"), FCh.ffi("1,0,x"), FCh.ffi("1,0,1,x"), FCh.ffi("2,3,"), FCh.ffi("2,2,x"), FCh.ffi("2,2,Tx")] == [ch_err("child: bad fate"), ch_err("child: bad id"), ch_err("child: input left over"), ch_err("child: bad phase"), ch_err("child: bad delete flag"), ch_err("child: input left over")] : List<&2, String>}

# LAW child_req_fits_example: witness: a request of each kind fits the wire (child_ffi_answers is not vacuous)
law child_req_fits_example:
  {[ch_req_fits(FCh.AskVerdict{Ch.Cfg{100n, 3n}, Ch.W{Some{7n}, 50n, 2n}, 10n, Ch.Busy{Some{7n}}, Ch.Inbox{}}), ch_req_fits(FCh.AskMove{None{}, 4n}), ch_req_fits(FCh.AskAbort{Ch.Owing{Ch.Stalled{}, 4n}, True{}})] == [True{}, True{}, True{}] : List<&2, Bool>}
