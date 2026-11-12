# eukhe: lemmas the proofs of laws/run/spec.bend share: the entry's
# decoder is the laws' reader, stage by stage (rex.ask); the entry's
# encoders are the laws' spellers (rex.w_*); its answer is the rules'
# decision, spelled (rex.answer); so the entry is the laws' entry on every
# input (rex.exact)

import Base
import ../../../bend/ffi_run.bend as FRn
import ../../../bend/run/decision.bend as RnDecision
import ../../../bend/run/recovery.bend as RnRecovery
import ../../../bend/run/state.bend as RnState
import ../../../bend/wire.bend as Wr
import ../../../laws/run/model.bend as Run
import ../../../laws/run/spec.bend as RunSpec
import ../run_reply_is_the_rust_rule.bend as PRunReplyIsTheRustRule
import ../run_prepare_is_the_rust_rule.bend as PRunPrepareIsTheRustRule
import ../run_compact_is_the_rust_rule.bend as PRunCompactIsTheRustRule
import ../run_round_is_the_rust_rule.bend as PRunRoundIsTheRustRule
import ../rec_recover_is_the_rust_rule.bend as PRecRecoverIsTheRustRule

# The reader
# ----------

def rex.lim3(+rounds: Nat, +wait: Nat, +retries: Nat, d: Wr.Dec<Nat>) -> {FRn.get_lim.f3(rounds, wait, retries, d) == RunSpec.re.r_lim.notes(rounds, wait, retries, d) : Wr.Dec<RnDecision.Lim>}:
  match d:
    case Wr.Got{notes, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.lim2(+rounds: Nat, +wait: Nat, d: Wr.Dec<Nat>) -> {FRn.get_lim.f2(rounds, wait, d) == RunSpec.re.r_lim.retries(rounds, wait, d) : Wr.Dec<RnDecision.Lim>}:
  match d:
    case Wr.Got{retries, r}:
      rex.lim3(rounds, wait, retries, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.lim1(+rounds: Nat, d: Wr.Dec<Nat>) -> {FRn.get_lim.f1(rounds, d) == RunSpec.re.r_lim.wait(rounds, d) : Wr.Dec<RnDecision.Lim>}:
  match d:
    case Wr.Got{wait, r}:
      rex.lim2(rounds, wait, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.lim0(d: Wr.Dec<Nat>) -> {FRn.get_lim.f0(d) == RunSpec.re.r_lim.rounds(d) : Wr.Dec<RnDecision.Lim>}:
  match d:
    case Wr.Got{rounds, r}:
      rex.lim1(rounds, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.lim(+s: String) -> {FRn.get_lim(s) == RunSpec.re.r_lim(s) : Wr.Dec<RnDecision.Lim>}:
  rex.lim0(Wr.get_nat(s))

def rex.at3(+attempt: Nat, +notes: Nat, +waited: Nat, d: Wr.Dec<Bool>) -> {FRn.get_at.f3(attempt, notes, waited, d) == RunSpec.re.r_at.compacted(attempt, notes, waited, d) : Wr.Dec<RnDecision.At>}:
  match d:
    case Wr.Got{compacted, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.at2(+attempt: Nat, +notes: Nat, d: Wr.Dec<Nat>) -> {FRn.get_at.f2(attempt, notes, d) == RunSpec.re.r_at.waited(attempt, notes, d) : Wr.Dec<RnDecision.At>}:
  match d:
    case Wr.Got{waited, r}:
      rex.at3(attempt, notes, waited, Wr.get_bool(r))
    case Wr.Bad{}:
      {==}

def rex.at1(+attempt: Nat, d: Wr.Dec<Nat>) -> {FRn.get_at.f1(attempt, d) == RunSpec.re.r_at.notes(attempt, d) : Wr.Dec<RnDecision.At>}:
  match d:
    case Wr.Got{notes, r}:
      rex.at2(attempt, notes, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.at0(d: Wr.Dec<Nat>) -> {FRn.get_at.f0(d) == RunSpec.re.r_at.attempt(d) : Wr.Dec<RnDecision.At>}:
  match d:
    case Wr.Got{attempt, r}:
      rex.at1(attempt, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.at(+s: String) -> {FRn.get_at(s) == RunSpec.re.r_at(s) : Wr.Dec<RnDecision.At>}:
  rex.at0(Wr.get_nat(s))

def rex.reply_noted(+retryable: Bool, d: Wr.Dec<Bool>) -> {FRn.get_reply.c3.f1(retryable, d) == RunSpec.re.r_reply.noted(retryable, d) : Wr.Dec<RnState.Reply>}:
  match d:
    case Wr.Got{noted, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.reply_retryable(d: Wr.Dec<Bool>) -> {FRn.get_reply.c3.f0(d) == RunSpec.re.r_reply.retryable(d) : Wr.Dec<RnState.Reply>}:
  match d:
    case Wr.Got{retryable, r}:
      rex.reply_noted(retryable, Wr.get_bool(r))
    case Wr.Bad{}:
      {==}

def rex.reply_cut(d: Wr.Dec<Bool>) -> {FRn.get_reply.c4.f0(d) == RunSpec.re.r_reply.cut(d) : Wr.Dec<RnState.Reply>}:
  match d:
    case Wr.Got{cut, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.reply_tag(d: Wr.Dec<Nat>) -> {FRn.get_reply.tag(d) == RunSpec.re.r_reply.tag(d) : Wr.Dec<RnState.Reply>}:
  match d:
    case Wr.Got{t, +r}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          rex.reply_retryable(Wr.get_bool(r))
        case 4n:
          rex.reply_cut(Wr.get_bool(r))
        case 5n+u:
          {==}
    case Wr.Bad{}:
      {==}

def rex.reply(+s: String) -> {FRn.get_reply(s) == RunSpec.re.r_reply(s) : Wr.Dec<RnState.Reply>}:
  rex.reply_tag(Wr.get_nat(s))

def rex.ended1(+text: Bool, d: Wr.Dec<Bool>) -> {FRn.get_ended.f1(text, d) == RunSpec.re.r_ended.calls(text, d) : Wr.Dec<RnState.Ended>}:
  match d:
    case Wr.Got{calls, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.ended0(d: Wr.Dec<Bool>) -> {FRn.get_ended.f0(d) == RunSpec.re.r_ended.text(d) : Wr.Dec<RnState.Ended>}:
  match d:
    case Wr.Got{text, r}:
      rex.ended1(text, Wr.get_bool(r))
    case Wr.Bad{}:
      {==}

def rex.ended_req(+s: String) -> {FRn.get_ended(s) == RunSpec.re.r_ended(s) : Wr.Dec<RnState.Ended>}:
  rex.ended0(Wr.get_bool(s))

def rex.th_tag(d: Wr.Dec<Nat>) -> {FRn.get_th.tag(d) == RunSpec.re.r_th.tag(d) : Wr.Dec<RnDecision.Th>}:
  match d:
    case Wr.Got{t, r}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def rex.th(+s: String) -> {FRn.get_th(s) == RunSpec.re.r_th(s) : Wr.Dec<RnDecision.Th>}:
  rex.th_tag(Wr.get_nat(s))

def rex.got_tag(d: Wr.Dec<Nat>) -> {FRn.get_got.tag(d) == RunSpec.re.r_got.tag(d) : Wr.Dec<RnState.Got>}:
  match d:
    case Wr.Got{t, r}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n+u:
          {==}
    case Wr.Bad{}:
      {==}

def rex.got(+s: String) -> {FRn.get_got(s) == RunSpec.re.r_got(s) : Wr.Dec<RnState.Got>}:
  rex.got_tag(Wr.get_nat(s))

def rex.rcfg3(+long: Nat, +leak: Nat, +redirect: Nat, d: Wr.Dec<Nat>) -> {FRn.get_rcfg.f3(long, leak, redirect, d) == RunSpec.re.r_rcfg.repeat(long, leak, redirect, d) : Wr.Dec<RnRecovery.RCfg>}:
  match d:
    case Wr.Got{repeat, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.rcfg2(+long: Nat, +leak: Nat, d: Wr.Dec<Nat>) -> {FRn.get_rcfg.f2(long, leak, d) == RunSpec.re.r_rcfg.redirect(long, leak, d) : Wr.Dec<RnRecovery.RCfg>}:
  match d:
    case Wr.Got{redirect, r}:
      rex.rcfg3(long, leak, redirect, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.rcfg1(+long: Nat, d: Wr.Dec<Nat>) -> {FRn.get_rcfg.f1(long, d) == RunSpec.re.r_rcfg.leak(long, d) : Wr.Dec<RnRecovery.RCfg>}:
  match d:
    case Wr.Got{leak, r}:
      rex.rcfg2(long, leak, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.rcfg0(d: Wr.Dec<Nat>) -> {FRn.get_rcfg.f0(d) == RunSpec.re.r_rcfg.long(d) : Wr.Dec<RnRecovery.RCfg>}:
  match d:
    case Wr.Got{long, r}:
      rex.rcfg1(long, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.rcfg(+s: String) -> {FRn.get_rcfg(s) == RunSpec.re.r_rcfg(s) : Wr.Dec<RnRecovery.RCfg>}:
  rex.rcfg0(Wr.get_nat(s))

def rex.stuck_before(d: Wr.Dec<Nat>) -> {FRn.get_stuck.c2.f0(d) == RunSpec.re.r_stuck.before(d) : Wr.Dec<RnDecision.Stuck>}:
  match d:
    case Wr.Got{before, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.stuck5(+w: Nat, +c: Nat, +p: Nat, +o: Nat, +cu: Bool, d: Wr.Dec<Bool>) -> {FRn.get_stuck.c0.f5(w, c, p, o, cu, d) == RunSpec.re.r_stuck.lower(w, c, p, o, cu, d) : Wr.Dec<RnDecision.Stuck>}:
  match d:
    case Wr.Got{lower, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.stuck4(+w: Nat, +c: Nat, +p: Nat, +o: Nat, d: Wr.Dec<Bool>) -> {FRn.get_stuck.c0.f4(w, c, p, o, d) == RunSpec.re.r_stuck.cuttable(w, c, p, o, d) : Wr.Dec<RnDecision.Stuck>}:
  match d:
    case Wr.Got{cu, r}:
      rex.stuck5(w, c, p, o, cu, Wr.get_bool(r))
    case Wr.Bad{}:
      {==}

def rex.stuck3(+w: Nat, +c: Nat, +p: Nat, d: Wr.Dec<Nat>) -> {FRn.get_stuck.c0.f3(w, c, p, d) == RunSpec.re.r_stuck.out(w, c, p, d) : Wr.Dec<RnDecision.Stuck>}:
  match d:
    case Wr.Got{o, r}:
      rex.stuck4(w, c, p, o, Wr.get_bool(r))
    case Wr.Bad{}:
      {==}

def rex.stuck2(+w: Nat, +c: Nat, d: Wr.Dec<Nat>) -> {FRn.get_stuck.c0.f2(w, c, d) == RunSpec.re.r_stuck.prompt(w, c, d) : Wr.Dec<RnDecision.Stuck>}:
  match d:
    case Wr.Got{p, r}:
      rex.stuck3(w, c, p, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.stuck1(+w: Nat, d: Wr.Dec<Nat>) -> {FRn.get_stuck.c0.f1(w, d) == RunSpec.re.r_stuck.catalog(w, d) : Wr.Dec<RnDecision.Stuck>}:
  match d:
    case Wr.Got{c, r}:
      rex.stuck2(w, c, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.stuck0(d: Wr.Dec<Nat>) -> {FRn.get_stuck.c0.f0(d) == RunSpec.re.r_stuck.window(d) : Wr.Dec<RnDecision.Stuck>}:
  match d:
    case Wr.Got{w, r}:
      rex.stuck1(w, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.stuck_tag(d: Wr.Dec<Nat>) -> {FRn.get_stuck.tag(d) == RunSpec.re.r_stuck.tag(d) : Wr.Dec<RnDecision.Stuck>}:
  match d:
    case Wr.Got{t, +r}:
      match t:
        case 0n:
          rex.stuck0(Wr.get_nat(r))
        case 1n:
          {==}
        case 2n:
          rex.stuck_before(Wr.get_nat(r))
        case 3n:
          {==}
        case 4n+u:
          {==}
    case Wr.Bad{}:
      {==}

def rex.stuck(+s: String) -> {FRn.get_stuck(s) == RunSpec.re.r_stuck(s) : Wr.Dec<RnDecision.Stuck>}:
  rex.stuck_tag(Wr.get_nat(s))

def rex.rk_tag(d: Wr.Dec<Nat>) -> {FRn.get_rk.tag(d) == RunSpec.re.r_rk.tag(d) : Wr.Dec<RnRecovery.Rk>}:
  match d:
    case Wr.Got{t, r}:
      match t:
        case 0n:
          {==}
        case 1n:
          {==}
        case 2n:
          {==}
        case 3n:
          {==}
        case 4n:
          {==}
        case 5n+u:
          {==}
    case Wr.Bad{}:
      {==}

def rex.rk(+s: String) -> {FRn.get_rk(s) == RunSpec.re.r_rk(s) : Wr.Dec<RnRecovery.Rk>}:
  rex.rk_tag(Wr.get_nat(s))

def rex.a0_reply(+l: RnDecision.Lim, +t: RnDecision.At, d: Wr.Dec<RnState.Reply>) -> {FRn.get_ask.c0.f2(l, t, d) == RunSpec.re.r_ask.reply_reply(l, t, d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{reply, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.a0_at(+l: RnDecision.Lim, d: Wr.Dec<RnDecision.At>) -> {FRn.get_ask.c0.f1(l, d) == RunSpec.re.r_ask.reply_at(l, d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{+t, +r}:
      %Equal.sym(Wr.Dec<RnState.Reply>, FRn.get_reply(r), RunSpec.re.r_reply(r), rex.reply(r)) : {FRn.get_ask.c0.f2(l, t, _) == RunSpec.re.r_ask.reply_reply(l, t, RunSpec.re.r_reply(r)) : Wr.Dec<FRn.Ask>}
      rex.a0_reply(l, t, RunSpec.re.r_reply(r))
    case Wr.Bad{}:
      {==}

def rex.a0_lim(d: Wr.Dec<RnDecision.Lim>) -> {FRn.get_ask.c0.f0(d) == RunSpec.re.r_ask.reply_lim(d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{+l, +r}:
      %Equal.sym(Wr.Dec<RnDecision.At>, FRn.get_at(r), RunSpec.re.r_at(r), rex.at(r)) : {FRn.get_ask.c0.f1(l, _) == RunSpec.re.r_ask.reply_at(l, RunSpec.re.r_at(r)) : Wr.Dec<FRn.Ask>}
      rex.a0_at(l, RunSpec.re.r_at(r))
    case Wr.Bad{}:
      {==}

def rex.a1(d: Wr.Dec<RnState.Ended>) -> {FRn.get_ask.c1.f0(d) == RunSpec.re.r_ask.ended(d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{m, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.a2_th(+compacted: Bool, d: Wr.Dec<RnDecision.Th>) -> {FRn.get_ask.c2.f1(compacted, d) == RunSpec.re.r_ask.prepare_th(compacted, d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{th, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.a2(d: Wr.Dec<Bool>) -> {FRn.get_ask.c2.f0(d) == RunSpec.re.r_ask.prepare(d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{+compacted, +r}:
      %Equal.sym(Wr.Dec<RnDecision.Th>, FRn.get_th(r), RunSpec.re.r_th(r), rex.th(r)) : {FRn.get_ask.c2.f1(compacted, _) == RunSpec.re.r_ask.prepare_th(compacted, RunSpec.re.r_th(r)) : Wr.Dec<FRn.Ask>}
      rex.a2_th(compacted, RunSpec.re.r_th(r))
    case Wr.Bad{}:
      {==}

def rex.a3_got(+over: Bool, d: Wr.Dec<RnState.Got>) -> {FRn.get_ask.c3.f1(over, d) == RunSpec.re.r_ask.compact_got(over, d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{got, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.a3(d: Wr.Dec<Bool>) -> {FRn.get_ask.c3.f0(d) == RunSpec.re.r_ask.compact(d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{+over, +r}:
      %Equal.sym(Wr.Dec<RnState.Got>, FRn.get_got(r), RunSpec.re.r_got(r), rex.got(r)) : {FRn.get_ask.c3.f1(over, _) == RunSpec.re.r_ask.compact_got(over, RunSpec.re.r_got(r)) : Wr.Dec<FRn.Ask>}
      rex.a3_got(over, RunSpec.re.r_got(r))
    case Wr.Bad{}:
      {==}

def rex.a4_reset(+l: RnDecision.Lim, +count: Nat, +stops: Bool, d: Wr.Dec<Bool>) -> {FRn.get_ask.c4.f3(l, count, stops, d) == RunSpec.re.r_ask.round_reset(l, count, stops, d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{reset, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.a4_stops(+l: RnDecision.Lim, +count: Nat, d: Wr.Dec<Bool>) -> {FRn.get_ask.c4.f2(l, count, d) == RunSpec.re.r_ask.round_stops(l, count, d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{stops, r}:
      rex.a4_reset(l, count, stops, Wr.get_bool(r))
    case Wr.Bad{}:
      {==}

def rex.a4_count(+l: RnDecision.Lim, d: Wr.Dec<Nat>) -> {FRn.get_ask.c4.f1(l, d) == RunSpec.re.r_ask.round_count(l, d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{count, r}:
      rex.a4_stops(l, count, Wr.get_bool(r))
    case Wr.Bad{}:
      {==}

def rex.a4(d: Wr.Dec<RnDecision.Lim>) -> {FRn.get_ask.c4.f0(d) == RunSpec.re.r_ask.round_lim(d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{l, r}:
      rex.a4_count(l, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.a5_row(+rc: RnRecovery.RCfg, +st: RnDecision.Stuck, +k: RnRecovery.Rk, d: Wr.Dec<Nat>) -> {FRn.get_ask.c5.f3(rc, st, k, d) == RunSpec.re.r_ask.recover_row(rc, st, k, d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{row, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.a5_rk(+rc: RnRecovery.RCfg, +st: RnDecision.Stuck, d: Wr.Dec<RnRecovery.Rk>) -> {FRn.get_ask.c5.f2(rc, st, d) == RunSpec.re.r_ask.recover_rk(rc, st, d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{k, r}:
      rex.a5_row(rc, st, k, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.a5_stuck(+rc: RnRecovery.RCfg, d: Wr.Dec<RnDecision.Stuck>) -> {FRn.get_ask.c5.f1(rc, d) == RunSpec.re.r_ask.recover_stuck(rc, d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{+st, +r}:
      %Equal.sym(Wr.Dec<RnRecovery.Rk>, FRn.get_rk(r), RunSpec.re.r_rk(r), rex.rk(r)) : {FRn.get_ask.c5.f2(rc, st, _) == RunSpec.re.r_ask.recover_rk(rc, st, RunSpec.re.r_rk(r)) : Wr.Dec<FRn.Ask>}
      rex.a5_rk(rc, st, RunSpec.re.r_rk(r))
    case Wr.Bad{}:
      {==}

def rex.a5(d: Wr.Dec<RnRecovery.RCfg>) -> {FRn.get_ask.c5.f0(d) == RunSpec.re.r_ask.recover_rcfg(d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{+rc, +r}:
      %Equal.sym(Wr.Dec<RnDecision.Stuck>, FRn.get_stuck(r), RunSpec.re.r_stuck(r), rex.stuck(r)) : {FRn.get_ask.c5.f1(rc, _) == RunSpec.re.r_ask.recover_stuck(rc, RunSpec.re.r_stuck(r)) : Wr.Dec<FRn.Ask>}
      rex.a5_stuck(rc, RunSpec.re.r_stuck(r))
    case Wr.Bad{}:
      {==}

def rex.a6_retries(+retryable: Bool, +failures: Nat, d: Wr.Dec<Nat>) -> {FRn.get_ask.c6.f2(retryable, failures, d) == RunSpec.re.r_ask.poll_retries(retryable, failures, d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{retries, r}:
      {==}
    case Wr.Bad{}:
      {==}

def rex.a6_failures(+retryable: Bool, d: Wr.Dec<Nat>) -> {FRn.get_ask.c6.f1(retryable, d) == RunSpec.re.r_ask.poll_failures(retryable, d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{failures, r}:
      rex.a6_retries(retryable, failures, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.a6(d: Wr.Dec<Bool>) -> {FRn.get_ask.c6.f0(d) == RunSpec.re.r_ask.poll(d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{retryable, r}:
      rex.a6_failures(retryable, Wr.get_nat(r))
    case Wr.Bad{}:
      {==}

def rex.ask_tag(d: Wr.Dec<Nat>) -> {FRn.get_ask.tag(d) == RunSpec.re.r_ask.tag(d) : Wr.Dec<FRn.Ask>}:
  match d:
    case Wr.Got{t, +r}:
      match t:
        case 0n:
          %Equal.sym(Wr.Dec<RnDecision.Lim>, FRn.get_lim(r), RunSpec.re.r_lim(r), rex.lim(r)) : {FRn.get_ask.c0.f0(_) == RunSpec.re.r_ask.reply_lim(RunSpec.re.r_lim(r)) : Wr.Dec<FRn.Ask>}
          rex.a0_lim(RunSpec.re.r_lim(r))
        case 1n:
          %Equal.sym(Wr.Dec<RnState.Ended>, FRn.get_ended(r), RunSpec.re.r_ended(r), rex.ended_req(r)) : {FRn.get_ask.c1.f0(_) == RunSpec.re.r_ask.ended(RunSpec.re.r_ended(r)) : Wr.Dec<FRn.Ask>}
          rex.a1(RunSpec.re.r_ended(r))
        case 2n:
          rex.a2(Wr.get_bool(r))
        case 3n:
          rex.a3(Wr.get_bool(r))
        case 4n:
          %Equal.sym(Wr.Dec<RnDecision.Lim>, FRn.get_lim(r), RunSpec.re.r_lim(r), rex.lim(r)) : {FRn.get_ask.c4.f0(_) == RunSpec.re.r_ask.round_lim(RunSpec.re.r_lim(r)) : Wr.Dec<FRn.Ask>}
          rex.a4(RunSpec.re.r_lim(r))
        case 5n:
          %Equal.sym(Wr.Dec<RnRecovery.RCfg>, FRn.get_rcfg(r), RunSpec.re.r_rcfg(r), rex.rcfg(r)) : {FRn.get_ask.c5.f0(_) == RunSpec.re.r_ask.recover_rcfg(RunSpec.re.r_rcfg(r)) : Wr.Dec<FRn.Ask>}
          rex.a5(RunSpec.re.r_rcfg(r))
        case 6n:
          rex.a6(Wr.get_bool(r))
        case 7n+u:
          {==}
    case Wr.Bad{}:
      {==}

# the entry reads every input as the laws' reader does
def rex.ask(+s: String) -> {FRn.get_ask(s) == RunSpec.re.r_ask(s) : Wr.Dec<FRn.Ask>}:
  rex.ask_tag(Wr.get_nat(s))

# The spellers
# ------------

def rex.w_lim(l: RnDecision.Lim, -rest: String) -> {FRn.put_lim(l, rest) == RunSpec.re.w_lim(l, rest) : String}:
  match l:
    case RnDecision.Lim{rounds, wait, retries, notes}:
      {==}

def rex.w_at(t: RnDecision.At, -rest: String) -> {FRn.put_at(t, rest) == RunSpec.re.w_at(t, rest) : String}:
  match t:
    case RnDecision.At{attempt, notes, waited, compacted}:
      {==}

def rex.w_reply(x: RnState.Reply, -rest: String) -> {FRn.put_reply(x, rest) == RunSpec.re.w_reply(x, rest) : String}:
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

def rex.w_ended(m: RnState.Ended, -rest: String) -> {FRn.put_ended(m, rest) == RunSpec.re.w_ended(m, rest) : String}:
  match m:
    case RnState.Ended{text, calls}:
      {==}

def rex.w_th(th: RnDecision.Th, -rest: String) -> {FRn.put_th(th, rest) == RunSpec.re.w_th(th, rest) : String}:
  match th:
    case RnDecision.Under{}:
      {==}
    case RnDecision.Background{}:
      {==}
    case RnDecision.Blocking{}:
      {==}

def rex.w_got(g: RnState.Got, -rest: String) -> {FRn.put_got(g, rest) == RunSpec.re.w_got(g, rest) : String}:
  match g:
    case RnState.Built{}:
      {==}
    case RnState.Kept{}:
      {==}
    case RnState.Broke{}:
      {==}

def rex.w_rcfg(c: RnRecovery.RCfg, -rest: String) -> {FRn.put_rcfg(c, rest) == RunSpec.re.w_rcfg(c, rest) : String}:
  match c:
    case RnRecovery.RCfg{long, leak, redirect, repeat}:
      {==}

def rex.w_stuck(s: RnDecision.Stuck, -rest: String) -> {FRn.put_stuck(s, rest) == RunSpec.re.w_stuck(s, rest) : String}:
  match s:
    case RnDecision.Thought{window, catalog, prompt, out, cuttable, lower}:
      {==}
    case RnDecision.Leaked{}:
      {==}
    case RnDecision.Repeats{before}:
      {==}
    case RnDecision.Emptied{}:
      {==}

def rex.w_rk(k: RnRecovery.Rk, -rest: String) -> {FRn.put_rk(k, rest) == RunSpec.re.w_rk(k, rest) : String}:
  match k:
    case RnRecovery.Free{}:
      {==}
    case RnRecovery.Longs{}:
      {==}
    case RnRecovery.Leaks{}:
      {==}
    case RnRecovery.Loops{}:
      {==}
    case RnRecovery.Empties{}:
      {==}

# the entry's encoder of a request is the laws' speller
def rex.w_ask(a: FRn.Ask, +rest: String) -> {FRn.put_ask(a, rest) == RunSpec.re.w_ask(a, rest) : String}:
  match a:
    case FRn.AskReply{+l, +t, +reply}:
      %Equal.sym(String, FRn.put_reply(reply, rest), RunSpec.re.w_reply(reply, rest), rex.w_reply(reply, rest)) : {Wr.put_nat(0n, FRn.put_lim(l, FRn.put_at(t, _))) == RunSpec.re.w_ask(FRn.AskReply{l, t, reply}, rest) : String}
      %Equal.sym(String, FRn.put_at(t, RunSpec.re.w_reply(reply, rest)), RunSpec.re.w_at(t, RunSpec.re.w_reply(reply, rest)), rex.w_at(t, RunSpec.re.w_reply(reply, rest))) : {Wr.put_nat(0n, FRn.put_lim(l, _)) == RunSpec.re.w_ask(FRn.AskReply{l, t, reply}, rest) : String}
      %Equal.sym(String, FRn.put_lim(l, RunSpec.re.w_at(t, RunSpec.re.w_reply(reply, rest))), RunSpec.re.w_lim(l, RunSpec.re.w_at(t, RunSpec.re.w_reply(reply, rest))), rex.w_lim(l, RunSpec.re.w_at(t, RunSpec.re.w_reply(reply, rest)))) : {Wr.put_nat(0n, _) == RunSpec.re.w_ask(FRn.AskReply{l, t, reply}, rest) : String}
      {==}
    case FRn.AskEnded{+m}:
      %Equal.sym(String, FRn.put_ended(m, rest), RunSpec.re.w_ended(m, rest), rex.w_ended(m, rest)) : {Wr.put_nat(1n, _) == RunSpec.re.w_ask(FRn.AskEnded{m}, rest) : String}
      {==}
    case FRn.AskPrepare{+compacted, +th}:
      %Equal.sym(String, FRn.put_th(th, rest), RunSpec.re.w_th(th, rest), rex.w_th(th, rest)) : {Wr.put_nat(2n, Wr.put_bool(compacted, _)) == RunSpec.re.w_ask(FRn.AskPrepare{compacted, th}, rest) : String}
      {==}
    case FRn.AskCompact{+over, +got}:
      %Equal.sym(String, FRn.put_got(got, rest), RunSpec.re.w_got(got, rest), rex.w_got(got, rest)) : {Wr.put_nat(3n, Wr.put_bool(over, _)) == RunSpec.re.w_ask(FRn.AskCompact{over, got}, rest) : String}
      {==}
    case FRn.AskRound{+l, +count, +stops, +reset}:
      %Equal.sym(String, FRn.put_lim(l, Wr.put_nat(count, Wr.put_bool(stops, Wr.put_bool(reset, rest)))), RunSpec.re.w_lim(l, Wr.put_nat(count, Wr.put_bool(stops, Wr.put_bool(reset, rest)))), rex.w_lim(l, Wr.put_nat(count, Wr.put_bool(stops, Wr.put_bool(reset, rest))))) : {Wr.put_nat(4n, _) == RunSpec.re.w_ask(FRn.AskRound{l, count, stops, reset}, rest) : String}
      {==}
    case FRn.AskRecover{+rc, +s, +k, +row}:
      %Equal.sym(String, FRn.put_rk(k, Wr.put_nat(row, rest)), RunSpec.re.w_rk(k, Wr.put_nat(row, rest)), rex.w_rk(k, Wr.put_nat(row, rest))) : {Wr.put_nat(5n, FRn.put_rcfg(rc, FRn.put_stuck(s, _))) == RunSpec.re.w_ask(FRn.AskRecover{rc, s, k, row}, rest) : String}
      %Equal.sym(String, FRn.put_stuck(s, RunSpec.re.w_rk(k, Wr.put_nat(row, rest))), RunSpec.re.w_stuck(s, RunSpec.re.w_rk(k, Wr.put_nat(row, rest))), rex.w_stuck(s, RunSpec.re.w_rk(k, Wr.put_nat(row, rest)))) : {Wr.put_nat(5n, FRn.put_rcfg(rc, _)) == RunSpec.re.w_ask(FRn.AskRecover{rc, s, k, row}, rest) : String}
      %Equal.sym(String, FRn.put_rcfg(rc, RunSpec.re.w_stuck(s, RunSpec.re.w_rk(k, Wr.put_nat(row, rest)))), RunSpec.re.w_rcfg(rc, RunSpec.re.w_stuck(s, RunSpec.re.w_rk(k, Wr.put_nat(row, rest)))), rex.w_rcfg(rc, RunSpec.re.w_stuck(s, RunSpec.re.w_rk(k, Wr.put_nat(row, rest))))) : {Wr.put_nat(5n, _) == RunSpec.re.w_ask(FRn.AskRecover{rc, s, k, row}, rest) : String}
      {==}
    case FRn.AskPoll{retryable, failures, retries}:
      {==}

# The answers
# -----------

def rex.w_then(x: RnDecision.Then) -> {FRn.put_then(x, "") == RunSpec.re.w_then(x) : String}:
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

def rex.w_prepared(x: RnDecision.Prepared) -> {FRn.put_prepared(x, "") == RunSpec.re.w_prepared(x) : String}:
  match x:
    case RnDecision.Waits{}:
      {==}
    case RnDecision.Sends{background}:
      {==}

def rex.w_end(x: RnDecision.End) -> {FRn.put_end(x, "") == RunSpec.re.w_end(x) : String}:
  match x:
    case RnDecision.EndStop{}:
      {==}
    case RnDecision.EndReset{}:
      {==}
    case RnDecision.EndCapped{}:
      {==}
    case RnDecision.EndNext{count}:
      {==}

def rex.w_help(x: RnDecision.Help) -> {FRn.put_help(x, "") == RunSpec.re.w_help(x) : String}:
  match x:
    case RnDecision.Runs{}:
      {==}
    case RnDecision.Redoes{row}:
      {==}
    case RnDecision.Quits{}:
      {==}
    case RnDecision.Compacts{}:
      {==}
    case RnDecision.Lowers{row}:
      {==}

# the reply every message makes is `Ended::reply`'s
def rex.ended(m: RnState.Ended) -> {RnState.Ended.reply(m) == RunSpec.re.rust_ended(m) : RnState.Reply}:
  match m:
    case RnState.Ended{text, calls}:
      match text calls:
        case text True{}:
          {==}
        case True{} False{}:
          {==}
        case False{} False{}:
          {==}

# whether a failed poll polls again is `PollFailure::next`'s
def rex.poll(retryable: Bool, -failures: Nat, -retries: Nat) -> {RnDecision.decide.poll(retryable, failures, retries) == RunSpec.re.rust_poll(retryable, failures, retries) : Bool}:
  match retryable:
    case True{}:
      {==}
    case False{}:
      {==}

# the entry's answer to every request is the rules' decision, spelled
def rex.answer(a: FRn.Ask) -> {FRn.answer(a) == RunSpec.re.answer(a) : String}:
  match a:
    case FRn.AskReply{+l, +t, +reply}:
      %Equal.sym(RnDecision.Then, RnDecision.decide.reply(l, t, reply), Run.rust.after_reply(l, t, reply), Run.run_reply_is_the_rust_rule(l, t, reply)) : {FRn.put_then(_, "") == RunSpec.re.w_then(Run.rust.after_reply(l, t, reply)) : String}
      rex.w_then(Run.rust.after_reply(l, t, reply))
    case FRn.AskEnded{+m}:
      %Equal.sym(RnState.Reply, RnState.Ended.reply(m), RunSpec.re.rust_ended(m), rex.ended(m)) : {FRn.put_reply(_, "") == RunSpec.re.w_reply(RunSpec.re.rust_ended(m), "") : String}
      rex.w_reply(RunSpec.re.rust_ended(m), "")
    case FRn.AskPrepare{+compacted, +th}:
      %Equal.sym(RnDecision.Prepared, RnDecision.decide.prepare(compacted, th), Run.rust.before_request(compacted, th), Run.run_prepare_is_the_rust_rule(compacted, th)) : {FRn.put_prepared(_, "") == RunSpec.re.w_prepared(Run.rust.before_request(compacted, th)) : String}
      rex.w_prepared(Run.rust.before_request(compacted, th))
    case FRn.AskCompact{+over, +got}:
      %Equal.sym(Bool, RnDecision.decide.compact(over, got), Run.rust.after_compaction(over, got), Run.run_compact_is_the_rust_rule(over, got)) : {Wr.put_bool(_, "") == Wr.put_bool(Run.rust.after_compaction(over, got), "") : String}
      {==}
    case FRn.AskRound{+l, +count, +stops, +reset}:
      %Equal.sym(RnDecision.End, RnDecision.decide.round(l, count, stops, reset), Run.rust.round_end(l, count, stops, reset), Run.run_round_is_the_rust_rule(l, count, stops, reset)) : {FRn.put_end(_, "") == RunSpec.re.w_end(Run.rust.round_end(l, count, stops, reset)) : String}
      rex.w_end(Run.rust.round_end(l, count, stops, reset))
    case FRn.AskRecover{+rc, +s, +k, +row}:
      %Equal.sym(RnDecision.Help, RnDecision.decide.recover(rc, s, k, row), Run.rust.recover(rc, s, k, row), Run.rec_recover_is_the_rust_rule(rc, s, k, row)) : {FRn.put_help(_, "") == RunSpec.re.w_help(Run.rust.recover(rc, s, k, row)) : String}
      rex.w_help(Run.rust.recover(rc, s, k, row))
    case FRn.AskPoll{+retryable, +failures, +retries}:
      %Equal.sym(Bool, RnDecision.decide.poll(retryable, failures, retries), RunSpec.re.rust_poll(retryable, failures, retries), rex.poll(retryable, failures, retries)) : {Wr.put_bool(_, "") == Wr.put_bool(RunSpec.re.rust_poll(retryable, failures, retries), "") : String}
      {==}

# The entry
# ---------

def rex.end(whole: Bool, +a: FRn.Ask) -> {FRn.ffi.end(whole, a) == RunSpec.re.entry.end(whole, a) : String}:
  match whole:
    case True{}:
      rex.answer(a)
    case False{}:
      {==}

def rex.go(d: Wr.Dec<FRn.Ask>) -> {FRn.ffi.go(d) == RunSpec.re.entry.go(d) : String}:
  match d:
    case Wr.Got{a, +r}:
      rex.end(Wr.end(r), a)
    case Wr.Bad{}:
      {==}

# the entry is the laws' entry on every input
def rex.exact(+s: String) -> {FRn.ffi(s) == RunSpec.re.entry(s) : String}:
  %Equal.sym(Wr.Dec<FRn.Ask>, FRn.get_ask(s), RunSpec.re.r_ask(s), rex.ask(s)) : {FRn.ffi.go(_) == RunSpec.re.entry(s) : String}
  rex.go(RunSpec.re.r_ask(s))
