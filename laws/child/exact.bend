# eukhe: the laws of area child: the child entry (K2) on requests spelled
# from the wire primitives, answered from the laws' own rules (K1's verdict
# of the watch, ChildActed, ChildMove, ChildAbort)

import Base
import ../../bend/child.bend as Ch
import ../../bend/ffi_child.bend as FCh
import ../../bend/wire.bend as Wr
import ../base.bend as LawsBase
import ./model.bend as ChildModel
import ./entry.bend as ChildEntry

# ---- the child entry: spelled requests (bend/ffi_child.bend, id 4) ----
#
# LAWS: the three decisions the Rust task asks of the compiled core (the
# watch's call on a poll, crates/eukhe-core/src/durable/children/watch.rs;
# the report phase's move and the abort, children/task.rs), on requests
# spelled from the primitives of bend/wire.bend (not the entry's own
# codecs), read by the laws' own reader, answered from the laws' own rules
# (ChildActed, ChildMove, ChildAbort of laws/child/model.bend, and the
# watch's verdict below).
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
#     (none left: Stalled) and one try fewer. K1 is carried, for every
#     request within the wire, by child_ffi_answers below (its answer is
#     K1's verdict, ch_look_spec) and, for every clock and elapsed ms, by
#     the laws of laws/child/model.bend (child_settled_child_ends_the_watch,
#     child_token_is_progress, child_other_token_is_progress,
#     child_progress_is_not_a_stall, child_quiet_poll_spends_time,
#     child_failed_poll_spends_try_and_time).
# K2: on every input that is exactly one request the entry answers the
#     decision spelled; on any other input exactly the error form naming
#     the first part that does not read ("child: bad request", "child:
#     unknown request", "child: bad settings", "child: bad clock", "child:
#     bad elapsed ms", "child: bad poll", "child: bad mode", "child: bad
#     fate", "child: bad id", "child: bad phase", "child: bad delete flag")
#     or, after a whole request, "child: input left over". K2 is carried by
#     the requirement laws of laws/child/entry.bend (child_entry_answers_spelled,
#     child_entry_left_over, child_entry_reads_only_requests,
#     child_entry_errors_named, child_entry_bad_* and child_entry_unknown_*)
#     and child_ffi_answers below.

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
        case Ch.PollFailed{}:
          ch_lost(tries, tok, left, e)
        case Ch.Answered{r}:
          ch_settled(r)
        case Ch.Broke{}:
          Ch.Owe{Ch.Failed{}}
        case Ch.Gone{}:
          Ch.Owe{Ch.Failed{}}

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

# a poll: Busy 0 (the token) | PollFailed 1 | Answered 2 (T|F replied) | Broke 3 | Gone 4
def ch_spell_obs(o: Ch.Obs, rest: String) -> String:
  match o:
    case Ch.Busy{t}:
      Wr.put_nat(0n, ch_spell_mnat(t, rest))
    case Ch.PollFailed{}:
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

# a submission's fate, if any: 0 none | 1, then Queued 0 | Withdrawn 1 |
# Placed 2 | Read 3
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
        case Ch.Read{}:
          Wr.put_nat(1n, Wr.put_nat(3n, rest))

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
      ch_spell_call(ChildModel.ChildActed(ch_look_spec(c, w, e, o), m))
    case FCh.AskMove{f, +n}:
      ch_spell_move(ChildModel.ChildMove(f, n))
    case FCh.AskAbort{p, d}:
      ch_spell_ph(ChildModel.ChildAbort(p, d), "")

# every number of a request fits the wire
def ch_req_fits(q: FCh.Req) -> Bool:
  match q:
    case FCh.AskVerdict{c, w, e, o, m}:
      Bool.and(ChildEntry.wire_cfg_fits(c), Bool.and(ChildEntry.wire_w_fits(w), Bool.and(LawsBase.wire_fits(e), ChildEntry.wire_obs_fits(o))))
    case FCh.AskMove{f, n}:
      LawsBase.wire_fits(n)
    case FCh.AskAbort{p, d}:
      ChildEntry.wire_ph_fits(p)

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
      Wr.Got{Ch.PollFailed{}, s}
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
    case 3n:
      Wr.Got{Some{Ch.Read{}}, s}
    case 4n+q:
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

# The reply (K2), as the proof of child_ffi_answers reads it
# ----------------------------------------------------------

def ch_spec.verdict.fin(whole: Bool, +c: Ch.Cfg, +w: Ch.W, +e: Nat, o: Ch.Obs, m: Ch.Mode) -> String:
  match whole:
    case True{}:
      ch_spell_call(ChildModel.ChildActed(ch_look_spec(c, w, e, o), m))
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
      ch_spell_move(ChildModel.ChildMove(f, n))
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
      ch_spell_ph(ChildModel.ChildAbort(p, d), "")
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
  {[FCh.ffi("1,0,4,"), FCh.ffi("1,1,0,4,"), FCh.ffi("1,1,1,4,"), FCh.ffi("1,1,2,4,"), FCh.ffi("1,1,3,4,"), FCh.ffi("2,0,1,7,50,3,T"), FCh.ffi("2,0,0,50,3,F"), FCh.ffi("2,1,3,4,T")] == ["0,4,", "1,", "2,5,", "3,", "3,", "1,2,1,", "2,", "1,3,4,"] : List<&2, String>} &
  {[FCh.ffi(""), FCh.ffi("3,"), FCh.ffi("0,x"), FCh.ffi("0,1,2,x"), FCh.ffi("0,1,2,0,5,5,x"), FCh.ffi("0,1,2,0,5,5,1,9,"), FCh.ffi("0,1,2,0,5,5,1,1,2,"), FCh.ffi("0,1,2,0,5,5,1,1,0,x")] == [ch_err("child: bad request"), ch_err("child: unknown request"), ch_err("child: bad settings"), ch_err("child: bad clock"), ch_err("child: bad elapsed ms"), ch_err("child: bad poll"), ch_err("child: bad mode"), ch_err("child: input left over")] : List<&2, String>} &
  {[FCh.ffi("1,2,"), FCh.ffi("1,0,x"), FCh.ffi("1,0,1,x"), FCh.ffi("2,3,"), FCh.ffi("2,2,x"), FCh.ffi("2,2,Tx")] == [ch_err("child: bad fate"), ch_err("child: bad id"), ch_err("child: input left over"), ch_err("child: bad phase"), ch_err("child: bad delete flag"), ch_err("child: input left over")] : List<&2, String>}

# LAW child_req_fits_example: witness: a request of each kind fits the wire (child_ffi_answers is not vacuous)
law child_req_fits_example:
  {[ch_req_fits(FCh.AskVerdict{Ch.Cfg{100n, 3n}, Ch.W{Some{7n}, 50n, 2n}, 10n, Ch.Busy{Some{7n}}, Ch.Inbox{}}), ch_req_fits(FCh.AskMove{None{}, 4n}), ch_req_fits(FCh.AskAbort{Ch.Owing{Ch.Stalled{}, 4n}, True{}})] == [True{}, True{}, True{}] : List<&2, Bool>}
