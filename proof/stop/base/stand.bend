# eukhe: lemmas shared by the proofs of the reply at a stop (R8): an
# answered run stays answered, counts no answer and sends no request
# (sts.stays, sts.none, sts.kept); every help of a Director that goes
# makes a reply that retries (sts.go); such a reply never answers the run
# (sts.never).

import Base
import ../../../bend/run/decision.bend as RnDecision
import ../../../bend/run/recovery.bend as RnRecovery
import ../../../bend/run/request.bend as RnRequest
import ../../../bend/run/state.bend as RnState
import ../../../bend/run/step.bend as RnStep
import ../../../bend/stop.bend as S
import ../base.bend as LA
import ../../../laws/stop.bend as Stop

# An answered run
# ---------------

# an answered run stays as it is, whatever inputs follow
def sts.stays(more: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {RnStep.run.go(more, cfg, RnState.St{RnState.Answered{}, r, c, a, n, p}) == RnState.St{RnState.Answered{}, r, c, a, n, p} : RnState.St}:
  match more:
    case Nil{}:
      {==}
    case e <> rest:
      sts.stays(rest, cfg, r, c, a, n, p)

# an answered run counts no further answer
def sts.none(more: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {Stop.answers.go(more, cfg, RnState.St{RnState.Answered{}, r, c, a, n, p}) == 0n : Nat}:
  match more:
    case Nil{}:
      {==}
    case e <> rest:
      sts.none(rest, cfg, r, c, a, n, p)

# an answered run sends, cuts and notes no request
def sts.kept(more: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, t: RnRequest.Reqs) -> {RnRequest.reqs.go(more, cfg, RnState.St{RnState.Answered{}, r, c, a, n, p}, t) == t : RnRequest.Reqs}:
  match more:
    case Nil{}:
      {==}
    case e <> rest:
      match t:
        case RnRequest.Reqs{ctx, k, note, log}:
          sts.kept(rest, cfg, r, c, a, n, p, RnRequest.Reqs{ctx, k, note, log})

# The help of a Director that goes
# --------------------------------

def sts.long(u: Bool, -n: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec, -pass: RnState.Reply) -> {Stop.retried(Stop.help_reply(RnDecision.Help.of(RnRecovery.rec.long(u, n, same, last, r)), False{}, pass)) == True{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def sts.leak(u: Bool, -n: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec, -pass: RnState.Reply) -> {Stop.retried(Stop.help_reply(RnDecision.Help.of(RnRecovery.rec.leak(u, n, same, last, r)), False{}, pass)) == True{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def sts.empty(u: Bool, -n: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec, -pass: RnState.Reply) -> {Stop.retried(Stop.help_reply(RnDecision.Help.of(RnRecovery.rec.empty(u, n, same, last, r)), False{}, pass)) == True{} : Bool}:
  match u:
    case True{}:
      {==}
    case False{}:
      {==}

def sts.think(s: Bool, u: Bool, l: Bool, -n: Nat, -same: Nat, -last: Nat, -r: RnRecovery.Rec, -pass: RnState.Reply) -> {Stop.retried(Stop.help_reply(RnDecision.Help.of(RnRecovery.rec.think(s, u, l, n, same, last, r)), True{}, pass)) == True{} : Bool}:
  match s:
    case True{}:
      {==}
    case False{}:
      match u:
        case True{}:
          {==}
        case False{}:
          match l:
            case True{}:
              {==}
            case False{}:
              {==}

# every Director that goes makes a reply that retries, whatever the
# recovery state and the ladder's facts
def sts.go(d: S.Dir, text: Bool, +rc: RnRecovery.RCfg, +k: RnRecovery.Rk, +row: Nat, +w: Nat, +ca: Nat, +pr: Nat, +o: Nat, cu: Bool, lo: Bool, -pass: RnState.Reply) -> {Stop.retried(Stop.go_reply(d, text, rc, k, row, w, ca, pr, o, cu, lo, pass)) == True{} : Bool}:
  match d:
    case S.LengthStop{}:
      match text:
        case True{}:
          sts.long(RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)), RnRecovery.Rk.longs(k, row), 0n, 0n, RnRecovery.Rec{k, row, 0n, 0n}, pass)
        case False{}:
          sts.think(Bool.and(cu, RnRecovery.bound(w, ca, pr, o)), RnRecovery.below(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc)), Bool.and(lo, Nat.is_eq(RnRecovery.Rk.longs(k, row), RnRecovery.RCfg.long(rc))), RnRecovery.Rk.longs(k, row), 0n, 0n, RnRecovery.Rec{k, row, 0n, 0n}, pass)
    case S.EmptyStop{}:
      sts.empty(RnRecovery.below(RnRecovery.Rk.empties(k, row), S.empty_cap()), RnRecovery.Rk.empties(k, row), 0n, 0n, RnRecovery.Rec{k, row, 0n, 0n}, pass)
    case S.MarkupStop{}:
      sts.leak(RnRecovery.below(RnRecovery.Rk.leaks(k, row), RnRecovery.RCfg.leak(rc)), RnRecovery.Rk.leaks(k, row), 0n, 0n, RnRecovery.Rec{k, row, 0n, 0n}, pass)
    case S.PendingWork{}:
      {==}

# A reply that retries
# --------------------

def sts.note(+cfg: RnState.Cfg, -r: Nat, -c: Nat, -a: Nat, n: Nat, -p: Nat) -> {Stop.answered(RnState.St.ph(RnStep.note(cfg, r, c, a, n, p))) == False{} : Bool}:
  match n:
    case 1n+m:
      {==}
    case 0n:
      {==}

def sts.retry(+cfg: RnState.Cfg, retryable: Bool, -r: Nat, -c: Nat, a: Nat, -n: Nat, -p: Nat) -> {Stop.answered(RnState.St.ph(RnStep.retry(cfg, retryable, r, c, a, n, p))) == False{} : Bool}:
  match retryable a:
    case True{} 1n+b:
      {==}
    case True{} 0n:
      {==}
    case False{} a:
      {==}

def sts.error(+cfg: RnState.Cfg, retryable: Bool, noted: Bool, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {Stop.answered(RnState.St.ph(RnStep.error(cfg, retryable, noted, r, c, a, n, p))) == False{} : Bool}:
  match noted:
    case True{}:
      sts.note(cfg, r, c, a, n, p)
    case False{}:
      sts.retry(cfg, retryable, r, c, a, n, p)

def sts.overflow(cut: Bool, -r: Nat, c: Nat, -a: Nat, -n: Nat, -p: Nat) -> {Stop.answered(RnState.St.ph(RnStep.overflow(cut, r, c, a, n, p))) == False{} : Bool}:
  match cut c:
    case True{} 1n+d:
      {==}
    case True{} 0n:
      {==}
    case False{} c:
      {==}

# a reply that retries never answers the run
def sts.never(+cfg: RnState.Cfg, q: RnState.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat, h: {Stop.retried(q) == True{} : Bool}) -> {Stop.answered(RnState.St.ph(RnStep.call(cfg, q, r, c, a, n, p))) == False{} : Bool}:
  match q:
    case RnState.Plain{}:
      LA.stb.absurd({Stop.answered(RnState.St.ph(RnStep.call(cfg, RnState.Plain{}, r, c, a, n, p))) == False{} : Bool}, h)
    case RnState.Calls{}:
      LA.stb.absurd({Stop.answered(RnState.St.ph(RnStep.call(cfg, RnState.Calls{}, r, c, a, n, p))) == False{} : Bool}, h)
    case RnState.Deferred{}:
      LA.stb.absurd({Stop.answered(RnState.St.ph(RnStep.call(cfg, RnState.Deferred{}, r, c, a, n, p))) == False{} : Bool}, h)
    case RnState.Error{retryable, noted}:
      sts.error(cfg, retryable, noted, r, c, a, n, p)
    case RnState.Overflow{cut}:
      sts.overflow(cut, r, c, a, n, p)
