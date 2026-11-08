# eukhe: the laws of area run, section spec: the entry of the compiled
# core for the run's decisions (bend/ffi_run.bend), stated against the
# Rust that calls it and the rules of laws/run/model.bend, never against the
# entry's own codec or answer

import Base
import ../../bend/ffi_run.bend as FRn
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/state.bend as RnState
import ../../bend/wire.bend as Wr
import ./entry.bend as Run
import ./model.bend as RunModel

# LAWS (H4.10): crates/eukhe-durable/src/harness/generation/decide.rs and
# deferred.rs ask the run's entry for one decision (entry.rs `ask`): they
# write the decision's tag (the order of entry.rs `Ask`), then its inputs
# with eukhe_bend::wire::Writer, and read the decision's value. Each law
# is an open claim about the function the core runs (FRn.ffi), stated
# with spellers and a reader built only from the wire primitives of
# bend/wire.bend, and with the rules decide.rs and deferred.rs wrote
# before the core took them over (rust.* of laws/run/model.bend and below):
#
# E1: every input that is exactly one request (the grammar below, as
#     decide.rs and deferred.rs write it) answers the rule's decision,
#     spelled as decide.rs and deferred.rs read it: the step after a
#     reply (`after_reply`), the reply a message makes (`Ended::reply`),
#     what preparation does (`before_request`), whether preparation goes
#     on after a compaction (`after_compaction`), how a round ends
#     (`round_end`), what a recovery does (`recover`), whether a failed
#     poll polls again (`PollFailure::next`).
# E2: a request with input left over answers exactly the error form
#     "run: input left over after the request"; any other input that is
#     no request answers exactly the error form "run: malformed request".
# Every input is free: any counts, any limits, any caps, any text.

# The rules with no rule of laws/run/model.bend
# ---------------------------------------

# `Ended::reply` (decide.rs): the reply a message that ends the model's
# turn makes: its calls when it has a tool call, whatever its stop reason;
# else an answer when it has text; with no text and no call the model gave
# no answer: a noted error the retry policy does not cure (H4.7)
def re.rust_ended(m: RnState.Ended) -> RnState.Reply:
  match m:
    case RnState.Ended{text, calls}:
      match text calls:
        case text True{}:
          RnState.Calls{}
        case True{} False{}:
          RnState.Plain{}
        case False{} False{}:
          RnState.Error{False{}, True{}}

# `PollFailure::next` (deferred.rs): a retryable failure after fewer than
# retry.maxRetries failures in a row polls the same job again; any other
# failure cancels the job
def re.rust_poll(retryable: Bool, failures: Nat, retries: Nat) -> Bool:
  match retryable:
    case True{}:
      Nat.is_lt(failures, retries)
    case False{}:
      False{}

# The requests, as decide.rs and deferred.rs write them
# -----------------------------------------------------

# `write_limits`: maxToolRounds, the job's ms, retry.maxRetries, MAX_NOTES
def re.w_lim(l: RnDecision.Lim, rest: String) -> String:
  match l:
    case RnDecision.Lim{rounds, wait, retries, notes}:
      Wr.put_nat(rounds, Wr.put_nat(wait, Wr.put_nat(retries, Wr.put_nat(notes, rest))))

# `Counts`: the attempt, the notes, the ms waited, compacted
def re.w_at(t: RnDecision.At, rest: String) -> String:
  match t:
    case RnDecision.At{attempt, notes, waited, compacted}:
      Wr.put_nat(attempt, Wr.put_nat(notes, Wr.put_nat(waited, Wr.put_bool(compacted, rest))))

# a reply: 0 text, 1 calls, 2 deferred, 3 an error (retryable, noted),
# 4 an overflow (cut); the reply of a message is read in the same grammar
def re.w_reply(x: RnState.Reply, rest: String) -> String:
  match x:
    case RnState.Plain{}:
      Wr.put_nat(0n, rest)
    case RnState.Calls{}:
      Wr.put_nat(1n, rest)
    case RnState.Deferred{}:
      Wr.put_nat(2n, rest)
    case RnState.Error{retryable, noted}:
      Wr.put_nat(3n, Wr.put_bool(retryable, Wr.put_bool(noted, rest)))
    case RnState.Overflow{cut}:
      Wr.put_nat(4n, Wr.put_bool(cut, rest))

# `Ended`: text, calls
def re.w_ended(m: RnState.Ended, rest: String) -> String:
  match m:
    case RnState.Ended{text, calls}:
      Wr.put_bool(text, Wr.put_bool(calls, rest))

# the threshold: 0 none, 1 background, 2 blocking
def re.w_th(th: RnDecision.Th, rest: String) -> String:
  match th:
    case RnDecision.Under{}:
      Wr.put_nat(0n, rest)
    case RnDecision.Background{}:
      Wr.put_nat(1n, rest)
    case RnDecision.Blocking{}:
      Wr.put_nat(2n, rest)

# `Compacted`: 0 an entry, 1 nothing, 2 failed
def re.w_got(g: RnState.Got, rest: String) -> String:
  match g:
    case RnState.Built{}:
      Wr.put_nat(0n, rest)
    case RnState.Kept{}:
      Wr.put_nat(1n, rest)
    case RnState.Broke{}:
      Wr.put_nat(2n, rest)

# `Caps`: length, leak, redirect, repeat
def re.w_rcfg(c: RnRecovery.RCfg, rest: String) -> String:
  match c:
    case RnRecovery.RCfg{long, leak, redirect, repeat}:
      Wr.put_nat(long, Wr.put_nat(leak, Wr.put_nat(redirect, Wr.put_nat(repeat, rest))))

# `Stuck`: 0 a length stop, 1 a leak, 2 calls (the rounds before), 3 an
# empty reply, 4 a length stop with no text (window, catalog, prompt,
# output, cuttable, lower)
def re.w_stuck(s: RnDecision.Stuck, rest: String) -> String:
  match s:
    case RnDecision.Truncated{}:
      Wr.put_nat(0n, rest)
    case RnDecision.Leaked{}:
      Wr.put_nat(1n, rest)
    case RnDecision.Repeats{before}:
      Wr.put_nat(2n, Wr.put_nat(before, rest))
    case RnDecision.Emptied{}:
      Wr.put_nat(3n, rest)
    case RnDecision.Thought{window, catalog, prompt, out, cuttable, lower}:
      Wr.put_nat(4n, Wr.put_nat(window, Wr.put_nat(catalog, Wr.put_nat(prompt, Wr.put_nat(out, Wr.put_bool(cuttable, Wr.put_bool(lower, rest)))))))

# the recovery the note counts: 0 none, 1 length, 2 leak, 3 redirect,
# 4 empty
def re.w_rk(k: RnRecovery.Rk, rest: String) -> String:
  match k:
    case RnRecovery.Free{}:
      Wr.put_nat(0n, rest)
    case RnRecovery.Longs{}:
      Wr.put_nat(1n, rest)
    case RnRecovery.Leaks{}:
      Wr.put_nat(2n, rest)
    case RnRecovery.Loops{}:
      Wr.put_nat(3n, rest)
    case RnRecovery.Empties{}:
      Wr.put_nat(4n, rest)

# a request: the tag of entry.rs `Ask`, then the inputs its writer writes
def re.w_ask(a: FRn.Ask, rest: String) -> String:
  match a:
    case FRn.AskReply{l, t, reply}:
      Wr.put_nat(0n, re.w_lim(l, re.w_at(t, re.w_reply(reply, rest))))
    case FRn.AskEnded{m}:
      Wr.put_nat(1n, re.w_ended(m, rest))
    case FRn.AskPrepare{compacted, th}:
      Wr.put_nat(2n, Wr.put_bool(compacted, re.w_th(th, rest)))
    case FRn.AskCompact{over, got}:
      Wr.put_nat(3n, Wr.put_bool(over, re.w_got(got, rest)))
    case FRn.AskRound{l, count, stops, reset}:
      Wr.put_nat(4n, re.w_lim(l, Wr.put_nat(count, Wr.put_bool(stops, Wr.put_bool(reset, rest)))))
    case FRn.AskRecover{rc, s, k, row}:
      Wr.put_nat(5n, re.w_rcfg(rc, re.w_stuck(s, re.w_rk(k, Wr.put_nat(row, rest)))))
    case FRn.AskPoll{retryable, failures, retries}:
      Wr.put_nat(6n, Wr.put_bool(retryable, Wr.put_nat(failures, Wr.put_nat(retries, rest))))

# The answers, as decide.rs and deferred.rs read them
# ---------------------------------------------------

# `Step`: 0 answer, 1 tools, 2 poll, 3 retry, 4 note, 5 compact, 6 fail
# on the model, 7 fail at the job's deadline
def re.w_then(x: RnDecision.Then) -> String:
  match x:
    case RnDecision.DoAnswer{}:
      Wr.put_nat(0n, "")
    case RnDecision.DoTools{}:
      Wr.put_nat(1n, "")
    case RnDecision.DoPoll{}:
      Wr.put_nat(2n, "")
    case RnDecision.DoRetry{}:
      Wr.put_nat(3n, "")
    case RnDecision.DoNote{}:
      Wr.put_nat(4n, "")
    case RnDecision.DoCompact{}:
      Wr.put_nat(5n, "")
    case RnDecision.DoFail{}:
      Wr.put_nat(6n, "")
    case RnDecision.DoLate{}:
      Wr.put_nat(7n, "")

# `Prepared`: 0 wait for the compaction, 1 send (background)
def re.w_prepared(x: RnDecision.Prepared) -> String:
  match x:
    case RnDecision.Waits{}:
      Wr.put_nat(0n, "")
    case RnDecision.Sends{background}:
      Wr.put_nat(1n, Wr.put_bool(background, ""))

# `RoundEnd`: 0 stop, 1 reset, 2 capped, 3 the next (rounds)
def re.w_end(x: RnDecision.End) -> String:
  match x:
    case RnDecision.EndStop{}:
      Wr.put_nat(0n, "")
    case RnDecision.EndReset{}:
      Wr.put_nat(1n, "")
    case RnDecision.EndCapped{}:
      Wr.put_nat(2n, "")
    case RnDecision.EndNext{count}:
      Wr.put_nat(3n, Wr.put_nat(count, ""))

# `Act`: 0 run, 1 redo (row), 2 quit, 3 compact, 4 lower (row)
def re.w_help(x: RnDecision.Help) -> String:
  match x:
    case RnDecision.Runs{}:
      Wr.put_nat(0n, "")
    case RnDecision.Redoes{row}:
      Wr.put_nat(1n, Wr.put_nat(row, ""))
    case RnDecision.Quits{}:
      Wr.put_nat(2n, "")
    case RnDecision.Compacts{}:
      Wr.put_nat(3n, "")
    case RnDecision.Lowers{row}:
      Wr.put_nat(4n, Wr.put_nat(row, ""))

# E1: the answer to a request: the rule's decision, spelled
def re.answer(a: FRn.Ask) -> String:
  match a:
    case FRn.AskReply{l, t, reply}:
      re.w_then(RunModel.rust.after_reply(l, t, reply))
    case FRn.AskEnded{m}:
      re.w_reply(re.rust_ended(m), "")
    case FRn.AskPrepare{compacted, th}:
      re.w_prepared(RunModel.rust.before_request(compacted, th))
    case FRn.AskCompact{over, got}:
      Wr.put_bool(RunModel.rust.after_compaction(over, got), "")
    case FRn.AskRound{l, count, stops, reset}:
      re.w_end(RunModel.rust.round_end(l, count, stops, reset))
    case FRn.AskRecover{rc, s, k, row}:
      re.w_help(RunModel.rust.recover(rc, s, k, row))
    case FRn.AskPoll{retryable, failures, retries}:
      Wr.put_bool(re.rust_poll(retryable, failures, retries), "")

# The reader of a request (the grammar above, read with the wire's
# decoders, one field at a time)
# -------------------------------------------------------------------

def re.r_lim.notes(rounds: Nat, wait: Nat, retries: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<RnDecision.Lim>:
  match d:
    case Wr.Got{notes, s}:
      Wr.Got{RnDecision.Lim{rounds, wait, retries, notes}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_lim.retries(rounds: Nat, wait: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<RnDecision.Lim>:
  match d:
    case Wr.Got{retries, s}:
      re.r_lim.notes(rounds, wait, retries, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_lim.wait(rounds: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<RnDecision.Lim>:
  match d:
    case Wr.Got{wait, s}:
      re.r_lim.retries(rounds, wait, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_lim.rounds(d: Wr.Dec<Nat>) -> Wr.Dec<RnDecision.Lim>:
  match d:
    case Wr.Got{rounds, s}:
      re.r_lim.wait(rounds, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_lim(s: String) -> Wr.Dec<RnDecision.Lim>:
  re.r_lim.rounds(Wr.get_nat(s))

def re.r_at.compacted(attempt: Nat, notes: Nat, waited: Nat, d: Wr.Dec<Bool>) -> Wr.Dec<RnDecision.At>:
  match d:
    case Wr.Got{compacted, s}:
      Wr.Got{RnDecision.At{attempt, notes, waited, compacted}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_at.waited(attempt: Nat, notes: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<RnDecision.At>:
  match d:
    case Wr.Got{waited, s}:
      re.r_at.compacted(attempt, notes, waited, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_at.notes(attempt: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<RnDecision.At>:
  match d:
    case Wr.Got{notes, s}:
      re.r_at.waited(attempt, notes, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_at.attempt(d: Wr.Dec<Nat>) -> Wr.Dec<RnDecision.At>:
  match d:
    case Wr.Got{attempt, s}:
      re.r_at.notes(attempt, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_at(s: String) -> Wr.Dec<RnDecision.At>:
  re.r_at.attempt(Wr.get_nat(s))

def re.r_reply.noted(retryable: Bool, d: Wr.Dec<Bool>) -> Wr.Dec<RnState.Reply>:
  match d:
    case Wr.Got{noted, s}:
      Wr.Got{RnState.Error{retryable, noted}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_reply.retryable(d: Wr.Dec<Bool>) -> Wr.Dec<RnState.Reply>:
  match d:
    case Wr.Got{retryable, s}:
      re.r_reply.noted(retryable, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_reply.cut(d: Wr.Dec<Bool>) -> Wr.Dec<RnState.Reply>:
  match d:
    case Wr.Got{cut, s}:
      Wr.Got{RnState.Overflow{cut}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_reply.tag(d: Wr.Dec<Nat>) -> Wr.Dec<RnState.Reply>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{RnState.Plain{}, s}
        case 1n:
          Wr.Got{RnState.Calls{}, s}
        case 2n:
          Wr.Got{RnState.Deferred{}, s}
        case 3n:
          re.r_reply.retryable(Wr.get_bool(s))
        case 4n:
          re.r_reply.cut(Wr.get_bool(s))
        case 5n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_reply(s: String) -> Wr.Dec<RnState.Reply>:
  re.r_reply.tag(Wr.get_nat(s))

def re.r_ended.calls(text: Bool, d: Wr.Dec<Bool>) -> Wr.Dec<RnState.Ended>:
  match d:
    case Wr.Got{calls, s}:
      Wr.Got{RnState.Ended{text, calls}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ended.text(d: Wr.Dec<Bool>) -> Wr.Dec<RnState.Ended>:
  match d:
    case Wr.Got{text, s}:
      re.r_ended.calls(text, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ended(s: String) -> Wr.Dec<RnState.Ended>:
  re.r_ended.text(Wr.get_bool(s))

def re.r_th.tag(d: Wr.Dec<Nat>) -> Wr.Dec<RnDecision.Th>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{RnDecision.Under{}, s}
        case 1n:
          Wr.Got{RnDecision.Background{}, s}
        case 2n:
          Wr.Got{RnDecision.Blocking{}, s}
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_th(s: String) -> Wr.Dec<RnDecision.Th>:
  re.r_th.tag(Wr.get_nat(s))

def re.r_got.tag(d: Wr.Dec<Nat>) -> Wr.Dec<RnState.Got>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{RnState.Built{}, s}
        case 1n:
          Wr.Got{RnState.Kept{}, s}
        case 2n:
          Wr.Got{RnState.Broke{}, s}
        case 3n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_got(s: String) -> Wr.Dec<RnState.Got>:
  re.r_got.tag(Wr.get_nat(s))

def re.r_rcfg.repeat(long: Nat, leak: Nat, redirect: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<RnRecovery.RCfg>:
  match d:
    case Wr.Got{repeat, s}:
      Wr.Got{RnRecovery.RCfg{long, leak, redirect, repeat}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_rcfg.redirect(long: Nat, leak: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<RnRecovery.RCfg>:
  match d:
    case Wr.Got{redirect, s}:
      re.r_rcfg.repeat(long, leak, redirect, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_rcfg.leak(long: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<RnRecovery.RCfg>:
  match d:
    case Wr.Got{leak, s}:
      re.r_rcfg.redirect(long, leak, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_rcfg.long(d: Wr.Dec<Nat>) -> Wr.Dec<RnRecovery.RCfg>:
  match d:
    case Wr.Got{long, s}:
      re.r_rcfg.leak(long, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_rcfg(s: String) -> Wr.Dec<RnRecovery.RCfg>:
  re.r_rcfg.long(Wr.get_nat(s))

def re.r_stuck.before(d: Wr.Dec<Nat>) -> Wr.Dec<RnDecision.Stuck>:
  match d:
    case Wr.Got{before, s}:
      Wr.Got{RnDecision.Repeats{before}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_stuck.lower(window: Nat, catalog: Nat, prompt: Nat, out: Nat, cuttable: Bool, d: Wr.Dec<Bool>) -> Wr.Dec<RnDecision.Stuck>:
  match d:
    case Wr.Got{lower, s}:
      Wr.Got{RnDecision.Thought{window, catalog, prompt, out, cuttable, lower}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_stuck.cuttable(window: Nat, catalog: Nat, prompt: Nat, out: Nat, d: Wr.Dec<Bool>) -> Wr.Dec<RnDecision.Stuck>:
  match d:
    case Wr.Got{cuttable, s}:
      re.r_stuck.lower(window, catalog, prompt, out, cuttable, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_stuck.out(window: Nat, catalog: Nat, prompt: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<RnDecision.Stuck>:
  match d:
    case Wr.Got{out, s}:
      re.r_stuck.cuttable(window, catalog, prompt, out, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_stuck.prompt(window: Nat, catalog: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<RnDecision.Stuck>:
  match d:
    case Wr.Got{prompt, s}:
      re.r_stuck.out(window, catalog, prompt, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_stuck.catalog(window: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<RnDecision.Stuck>:
  match d:
    case Wr.Got{catalog, s}:
      re.r_stuck.prompt(window, catalog, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_stuck.window(d: Wr.Dec<Nat>) -> Wr.Dec<RnDecision.Stuck>:
  match d:
    case Wr.Got{window, s}:
      re.r_stuck.catalog(window, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_stuck.tag(d: Wr.Dec<Nat>) -> Wr.Dec<RnDecision.Stuck>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{RnDecision.Truncated{}, s}
        case 1n:
          Wr.Got{RnDecision.Leaked{}, s}
        case 2n:
          re.r_stuck.before(Wr.get_nat(s))
        case 3n:
          Wr.Got{RnDecision.Emptied{}, s}
        case 4n:
          re.r_stuck.window(Wr.get_nat(s))
        case 5n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_stuck(s: String) -> Wr.Dec<RnDecision.Stuck>:
  re.r_stuck.tag(Wr.get_nat(s))

def re.r_rk.tag(d: Wr.Dec<Nat>) -> Wr.Dec<RnRecovery.Rk>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          Wr.Got{RnRecovery.Free{}, s}
        case 1n:
          Wr.Got{RnRecovery.Longs{}, s}
        case 2n:
          Wr.Got{RnRecovery.Leaks{}, s}
        case 3n:
          Wr.Got{RnRecovery.Loops{}, s}
        case 4n:
          Wr.Got{RnRecovery.Empties{}, s}
        case 5n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_rk(s: String) -> Wr.Dec<RnRecovery.Rk>:
  re.r_rk.tag(Wr.get_nat(s))

def re.r_ask.reply_reply(l: RnDecision.Lim, t: RnDecision.At, d: Wr.Dec<RnState.Reply>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{reply, s}:
      Wr.Got{FRn.AskReply{l, t, reply}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.reply_at(l: RnDecision.Lim, d: Wr.Dec<RnDecision.At>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{t, s}:
      re.r_ask.reply_reply(l, t, re.r_reply(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.reply_lim(d: Wr.Dec<RnDecision.Lim>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{l, s}:
      re.r_ask.reply_at(l, re.r_at(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.ended(d: Wr.Dec<RnState.Ended>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{m, s}:
      Wr.Got{FRn.AskEnded{m}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.prepare_th(compacted: Bool, d: Wr.Dec<RnDecision.Th>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{th, s}:
      Wr.Got{FRn.AskPrepare{compacted, th}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.prepare(d: Wr.Dec<Bool>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{compacted, s}:
      re.r_ask.prepare_th(compacted, re.r_th(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.compact_got(over: Bool, d: Wr.Dec<RnState.Got>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{got, s}:
      Wr.Got{FRn.AskCompact{over, got}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.compact(d: Wr.Dec<Bool>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{over, s}:
      re.r_ask.compact_got(over, re.r_got(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.round_reset(l: RnDecision.Lim, count: Nat, stops: Bool, d: Wr.Dec<Bool>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{reset, s}:
      Wr.Got{FRn.AskRound{l, count, stops, reset}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.round_stops(l: RnDecision.Lim, count: Nat, d: Wr.Dec<Bool>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{stops, s}:
      re.r_ask.round_reset(l, count, stops, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.round_count(l: RnDecision.Lim, d: Wr.Dec<Nat>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{count, s}:
      re.r_ask.round_stops(l, count, Wr.get_bool(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.round_lim(d: Wr.Dec<RnDecision.Lim>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{l, s}:
      re.r_ask.round_count(l, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.recover_row(rc: RnRecovery.RCfg, st: RnDecision.Stuck, k: RnRecovery.Rk, d: Wr.Dec<Nat>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{row, s}:
      Wr.Got{FRn.AskRecover{rc, st, k, row}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.recover_rk(rc: RnRecovery.RCfg, st: RnDecision.Stuck, d: Wr.Dec<RnRecovery.Rk>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{k, s}:
      re.r_ask.recover_row(rc, st, k, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.recover_stuck(rc: RnRecovery.RCfg, d: Wr.Dec<RnDecision.Stuck>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{st, s}:
      re.r_ask.recover_rk(rc, st, re.r_rk(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.recover_rcfg(d: Wr.Dec<RnRecovery.RCfg>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{rc, s}:
      re.r_ask.recover_stuck(rc, re.r_stuck(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.poll_retries(retryable: Bool, failures: Nat, d: Wr.Dec<Nat>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{retries, s}:
      Wr.Got{FRn.AskPoll{retryable, failures, retries}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.poll_failures(retryable: Bool, d: Wr.Dec<Nat>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{failures, s}:
      re.r_ask.poll_retries(retryable, failures, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.poll(d: Wr.Dec<Bool>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{retryable, s}:
      re.r_ask.poll_failures(retryable, Wr.get_nat(s))
    case Wr.Bad{}:
      Wr.Bad{}

def re.r_ask.tag(d: Wr.Dec<Nat>) -> Wr.Dec<FRn.Ask>:
  match d:
    case Wr.Got{t, s}:
      match t:
        case 0n:
          re.r_ask.reply_lim(re.r_lim(s))
        case 1n:
          re.r_ask.ended(re.r_ended(s))
        case 2n:
          re.r_ask.prepare(Wr.get_bool(s))
        case 3n:
          re.r_ask.compact(Wr.get_bool(s))
        case 4n:
          re.r_ask.round_lim(re.r_lim(s))
        case 5n:
          re.r_ask.recover_rcfg(re.r_rcfg(s))
        case 6n:
          re.r_ask.poll(Wr.get_bool(s))
        case 7n+u:
          Wr.Bad{}
    case Wr.Bad{}:
      Wr.Bad{}

# the request at the start of s, and the input after it
def re.r_ask(s: String) -> Wr.Dec<FRn.Ask>:
  re.r_ask.tag(Wr.get_nat(s))

# The entry
# ---------

def re.entry.end(whole: Bool, a: FRn.Ask) -> String:
  match whole:
    case True{}:
      re.answer(a)
    case False{}:
      Wr.err("run: input left over after the request")

def re.entry.go(d: Wr.Dec<FRn.Ask>) -> String:
  match d:
    case Wr.Got{a, s}:
      re.entry.end(Wr.end(s), a)
    case Wr.Bad{}:
      Wr.err("run: malformed request")

# E1-E2: the answer to the input s
def re.entry(s: String) -> String:
  re.entry.go(re.r_ask(s))

# Laws
# ----

# LAW run_ended_is_the_rust_rule (H4.7): the reply every message makes is
# the one `Ended::reply` made: its calls when it has one, else an answer
# when it has text, else a noted error
# EXCLUDES: a message with calls and text read as an answer, a message
#   with no text and no call read as an answer or as a transient error
law run_ended_is_the_rust_rule:
  for +m: RnState.Ended
  {RnState.Ended.reply(m) == re.rust_ended(m) : RnState.Reply}

# LAW run_poll_is_the_rust_rule (H4.4): whether any failed poll polls the
# same job again, after any failures in a row, under any retry cap, is
# what `PollFailure::next` decided
# EXCLUDES: a repoll after the cap (failures off by one), a repoll of a
#   failure the retry policy cannot cure
law run_poll_is_the_rust_rule:
  for retryable: Bool
  for +failures: Nat
  for +retries: Nat
  {RnDecision.decide.poll(retryable, failures, retries) == re.rust_poll(retryable, failures, retries) : Bool}

# LAW run_entry_exact (E1, E2): on every input the entry answers exactly
# what the requests' reader and the rules answer: the rule's decision for
# a request read whole, spelled; the left-over error for a request with
# input after it; the malformed error for any other input
# EXCLUDES: an entry that answers a decision of its own (a recovery past
#   its cap, a step, a round's end, a preparation, a compaction's or a
#   poll's verdict other than the rule's), a field read into another, a
#   tag read as another, an answer spelled another way, a malformed input
#   answered with a value or a default, another error text
law run_entry_exact:
  for +s: String
  {FRn.ffi(s) == re.entry(s) : String}

# LAW run_entry_reads (E1): the reader reads every request Rust writes,
# every Nat within the wire, back whole, and leaves the input after it
# EXCLUDES: a reader (and so an entry) that refuses a request Rust
#   writes, eats input after it or reads it as another request
law run_entry_reads:
  for +a: FRn.Ask
  for +rest: String
  for +h: {Run.run.ask_fits(a) == True{} : Bool}
  {re.r_ask(re.w_ask(a, rest)) == Wr.Got{a, rest} : Wr.Dec<FRn.Ask>}

# LAW run_entry_answers (E1): every request Rust writes, every Nat within
# the wire, answers the rule's decision, spelled as Rust reads it
# EXCLUDES: a request of any kind answered with another decision, a
#   default, or the error form
law run_entry_answers:
  for +a: FRn.Ask
  for +h: {Run.run.ask_fits(a) == True{} : Bool}
  {FRn.ffi(re.w_ask(a, "")) == re.answer(a) : String}

# LAW run_entry_example (E1, E2): anchor: the wire strings Rust writes and
# the answers it reads, one of each request: the third empty note in a
# row (row 3, the cap) quits, the second one (row 2) redoes with note 3;
# a deferred reply that waited less than its job polls; a message with
# no text and no call is a noted error; a blocking threshold waits; a
# threshold compaction that found nothing goes on; a round below the cap
# goes on with one more round; a failed retryable poll below the cap
# polls again; input left over; an unknown tag
# EXCLUDES: a field order other than Rust's, another answer spelling, an
#   empty reply redone past its cap
law run_entry_example:
  {[FRn.ffi("5,3,2,2,5,3,4,3,"), FRn.ffi("5,3,2,2,5,3,4,2,"), FRn.ffi("0,250,600000,3,4,1,0,10,F2,"), FRn.ffi("1,FF"), FRn.ffi("2,F2,"), FRn.ffi("3,F1,"), FRn.ffi("4,250,600000,3,4,7,FF"), FRn.ffi("6,T2,3,"), FRn.ffi("5,3,2,2,5,3,4,3,x"), FRn.ffi("7,")] == ["2,", "1,3,", "2,", "3,FT", "0,", "T", "3,8,", "T", Wr.err("run: input left over after the request"), Wr.err("run: malformed request")] : List<&2, String>}
