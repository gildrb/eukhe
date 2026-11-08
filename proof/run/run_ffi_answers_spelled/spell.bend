# eukhe: lemmas of LAW run_ffi_answers_spelled (also used by
# run_ffi_left_over_spelled and run_ffi_reads_only_requests): the entry's
# encoders write the grammar's spelling, field by field and tag by tag,
# and its answer is the spelled value of the decision

import Base
import ../../../bend/ffi_run.bend as FRn
import ../../../bend/run/decision.bend as RnDecision
import ../../../bend/run/recovery.bend as RnRecovery
import ../../../bend/run/state.bend as RnState
import ../../../bend/wire.bend as Wr
import ../../../laws/run/entry.bend as Run

# Requests
# --------

def sp.lim(l: RnDecision.Lim, +r: String) -> {FRn.put_lim(l, r) == Run.run_spell_lim(l, r) : String}:
  match l:
    case RnDecision.Lim{rounds, wait, retries, notes}:
      {==}

def sp.at(t: RnDecision.At, +r: String) -> {FRn.put_at(t, r) == Run.run_spell_at(t, r) : String}:
  match t:
    case RnDecision.At{attempt, notes, waited, compacted}:
      {==}

def sp.reply(x: RnState.Reply, +r: String) -> {FRn.put_reply(x, r) == Run.run_spell_reply(x, r) : String}:
  match x:
    case RnState.Plain{}:
      {==}
    case RnState.Calls{}:
      {==}
    case RnState.Deferred{}:
      {==}
    case RnState.Error{retryable, noted}:
      {==}
    case RnState.Overflow{cut}:
      {==}

def sp.ended(m: RnState.Ended, +r: String) -> {FRn.put_ended(m, r) == Run.run_spell_ended(m, r) : String}:
  match m:
    case RnState.Ended{text, calls}:
      {==}

def sp.th(x: RnDecision.Th, +r: String) -> {FRn.put_th(x, r) == Run.run_spell_th(x, r) : String}:
  match x:
    case RnDecision.Under{}:
      {==}
    case RnDecision.Background{}:
      {==}
    case RnDecision.Blocking{}:
      {==}

def sp.got(x: RnState.Got, +r: String) -> {FRn.put_got(x, r) == Run.run_spell_got(x, r) : String}:
  match x:
    case RnState.Built{}:
      {==}
    case RnState.Kept{}:
      {==}
    case RnState.Broke{}:
      {==}

def sp.rcfg(c: RnRecovery.RCfg, +r: String) -> {FRn.put_rcfg(c, r) == Run.run_spell_rcfg(c, r) : String}:
  match c:
    case RnRecovery.RCfg{long, leak, redirect, repeat}:
      {==}

def sp.stuck(x: RnDecision.Stuck, +r: String) -> {FRn.put_stuck(x, r) == Run.run_spell_stuck(x, r) : String}:
  match x:
    case RnDecision.Truncated{}:
      {==}
    case RnDecision.Leaked{}:
      {==}
    case RnDecision.Repeats{before}:
      {==}

def sp.rk(x: RnRecovery.Rk, +r: String) -> {FRn.put_rk(x, r) == Run.run_spell_rk(x, r) : String}:
  match x:
    case RnRecovery.Free{}:
      {==}
    case RnRecovery.Longs{}:
      {==}
    case RnRecovery.Leaks{}:
      {==}
    case RnRecovery.Loops{}:
      {==}

# the entry's encoder writes the grammar's spelling of every request
def sp.ask(a: FRn.Ask, +rest: String) -> {FRn.put_ask(a, rest) == Run.run_spell_ask(a, rest) : String}:
  match a:
    case FRn.AskReply{+l, +t, +reply}:
      %sp.reply(reply, rest) : {FRn.put_ask(FRn.AskReply{l, t, reply}, rest) == Wr.put_nat(0n, Run.run_spell_lim(l, Run.run_spell_at(t, _))) : String}
      %sp.at(t, FRn.put_reply(reply, rest)) : {FRn.put_ask(FRn.AskReply{l, t, reply}, rest) == Wr.put_nat(0n, Run.run_spell_lim(l, _)) : String}
      %sp.lim(l, FRn.put_at(t, FRn.put_reply(reply, rest))) : {FRn.put_ask(FRn.AskReply{l, t, reply}, rest) == Wr.put_nat(0n, _) : String}
      {==}
    case FRn.AskEnded{+m}:
      %sp.ended(m, rest) : {FRn.put_ask(FRn.AskEnded{m}, rest) == Wr.put_nat(1n, _) : String}
      {==}
    case FRn.AskPrepare{+compacted, +th}:
      %sp.th(th, rest) : {FRn.put_ask(FRn.AskPrepare{compacted, th}, rest) == Wr.put_nat(2n, Wr.put_bool(compacted, _)) : String}
      {==}
    case FRn.AskCompact{+over, +got}:
      %sp.got(got, rest) : {FRn.put_ask(FRn.AskCompact{over, got}, rest) == Wr.put_nat(3n, Wr.put_bool(over, _)) : String}
      {==}
    case FRn.AskRound{+l, +count, +stops, +reset}:
      %sp.lim(l, Wr.put_nat(count, Wr.put_bool(stops, Wr.put_bool(reset, rest)))) : {FRn.put_ask(FRn.AskRound{l, count, stops, reset}, rest) == Wr.put_nat(4n, _) : String}
      {==}
    case FRn.AskRecover{+rc, +s, +k, +row}:
      %sp.rk(k, Wr.put_nat(row, rest)) : {FRn.put_ask(FRn.AskRecover{rc, s, k, row}, rest) == Wr.put_nat(5n, Run.run_spell_rcfg(rc, Run.run_spell_stuck(s, _))) : String}
      %sp.stuck(s, FRn.put_rk(k, Wr.put_nat(row, rest))) : {FRn.put_ask(FRn.AskRecover{rc, s, k, row}, rest) == Wr.put_nat(5n, Run.run_spell_rcfg(rc, _)) : String}
      %sp.rcfg(rc, FRn.put_stuck(s, FRn.put_rk(k, Wr.put_nat(row, rest)))) : {FRn.put_ask(FRn.AskRecover{rc, s, k, row}, rest) == Wr.put_nat(5n, _) : String}
      {==}
    case FRn.AskPoll{retryable, failures, retries}:
      {==}

# Answers
# -------

def sp.then(x: RnDecision.Then, +r: String) -> {FRn.put_then(x, r) == Run.run_spell_then(x, r) : String}:
  match x:
    case RnDecision.DoAnswer{}:
      {==}
    case RnDecision.DoTools{}:
      {==}
    case RnDecision.DoPoll{}:
      {==}
    case RnDecision.DoRetry{}:
      {==}
    case RnDecision.DoNote{}:
      {==}
    case RnDecision.DoCompact{}:
      {==}
    case RnDecision.DoFail{}:
      {==}
    case RnDecision.DoLate{}:
      {==}

def sp.prepared(x: RnDecision.Prepared, +r: String) -> {FRn.put_prepared(x, r) == Run.run_spell_prepared(x, r) : String}:
  match x:
    case RnDecision.Waits{}:
      {==}
    case RnDecision.Sends{background}:
      {==}

def sp.end(x: RnDecision.End, +r: String) -> {FRn.put_end(x, r) == Run.run_spell_end(x, r) : String}:
  match x:
    case RnDecision.EndStop{}:
      {==}
    case RnDecision.EndReset{}:
      {==}
    case RnDecision.EndCapped{}:
      {==}
    case RnDecision.EndNext{count}:
      {==}

def sp.help(x: RnDecision.Help, +r: String) -> {FRn.put_help(x, r) == Run.run_spell_help(x, r) : String}:
  match x:
    case RnDecision.Runs{}:
      {==}
    case RnDecision.Redoes{row}:
      {==}
    case RnDecision.Stands{}:
      {==}
    case RnDecision.Quits{}:
      {==}

# the entry's answer to a request is the spelled value of its decision
def sp.answer(a: FRn.Ask) -> {FRn.answer(a) == Run.run_spell_answer(a) : String}:
  match a:
    case FRn.AskReply{l, t, reply}:
      sp.then(RnDecision.decide.reply(l, t, reply), "")
    case FRn.AskEnded{m}:
      sp.reply(RnState.Ended.reply(m), "")
    case FRn.AskPrepare{compacted, th}:
      sp.prepared(RnDecision.decide.prepare(compacted, th), "")
    case FRn.AskCompact{over, got}:
      {==}
    case FRn.AskRound{l, count, stops, reset}:
      sp.end(RnDecision.decide.round(l, count, stops, reset), "")
    case FRn.AskRecover{rc, s, k, row}:
      sp.help(RnDecision.decide.recover(rc, s, k, row), "")
    case FRn.AskPoll{retryable, failures, retries}:
      {==}
