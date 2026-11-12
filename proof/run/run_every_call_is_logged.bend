# eukhe: the proof of LAW run_every_call_is_logged
#
# PROOF: each step logs a sent request exactly when preparation ends in a call (lg.step, case by case); by induction on the inputs (lg.run).

import Base
import ../../bend/run/request.bend as RnRequest
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/model.bend as Run
import ./base.bend as LA

# a + b + c, either way
def lg.assoc(x: Nat, -b: Nat, -y: Nat) -> {Nat.add(Nat.add(x, b), y) == Nat.add(x, Nat.add(b, y)) : Nat}:
  match x:
    case 0n:
      {==}
    case 1n+z:
      %Equal.sym(Nat, Nat.add(Nat.add(z, b), y), Nat.add(z, Nat.add(b, y)), lg.assoc(z, b, y)) : {1n+_ == 1n+Nat.add(z, Nat.add(b, y)) : Nat}
      {==}

# one step logs a sent request exactly when preparation ends in a call
def lg.step(pb: RnState.Ph, e: RnState.Ev, pa: RnState.Ph, t: RnRequest.Reqs) -> {Run.sents(RnRequest.Reqs.log(RnRequest.Reqs.step(pb, e, pa, t))) == Nat.add(Run.sends_one(pb, pa), Run.sents(RnRequest.Reqs.log(t))) : Nat}:
  match pb:
    case RnState.Prepare{}:
      match pa:
        case RnState.Call{}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
        case RnState.Prepare{}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
        case RnState.Compact{over}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
        case RnState.Tools{}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
        case RnState.Answered{}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
        case RnState.Aborted{}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
        case RnState.Failed{why}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
    case RnState.Call{}:
      match e:
        case RnState.Abort{}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
        case RnState.Go{reply, fin, got}:
          match reply:
            case RnState.Error{retryable, noted}:
              match noted:
                case True{}:
                  match t:
                    case RnRequest.Reqs{ctx, n, note, log}:
                      {==}
                case False{}:
                  match t:
                    case RnRequest.Reqs{ctx, n, note, log}:
                      {==}
            case RnState.Plain{}:
              match t:
                case RnRequest.Reqs{ctx, n, note, log}:
                  {==}
            case RnState.Calls{}:
              match t:
                case RnRequest.Reqs{ctx, n, note, log}:
                  {==}
            case RnState.Deferred{}:
              match t:
                case RnRequest.Reqs{ctx, n, note, log}:
                  {==}
            case RnState.Overflow{cut}:
              match t:
                case RnRequest.Reqs{ctx, n, note, log}:
                  {==}
    case RnState.Compact{over}:
      match e:
        case RnState.Abort{}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
        case RnState.Go{reply, fin, got}:
          match got:
            case RnState.Built{}:
              match t:
                case RnRequest.Reqs{ctx, n, note, log}:
                  {==}
            case RnState.Kept{}:
              match t:
                case RnRequest.Reqs{ctx, n, note, log}:
                  {==}
            case RnState.Broke{}:
              match t:
                case RnRequest.Reqs{ctx, n, note, log}:
                  {==}
    case RnState.Tools{}:
      match pa:
        case RnState.Prepare{}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
        case RnState.Call{}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
        case RnState.Compact{over}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
        case RnState.Tools{}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
        case RnState.Answered{}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
        case RnState.Aborted{}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
        case RnState.Failed{why}:
          match t:
            case RnRequest.Reqs{ctx, n, note, log}:
              {==}
    case RnState.Answered{}:
      match t:
        case RnRequest.Reqs{ctx, n, note, log}:
          {==}
    case RnState.Aborted{}:
      match t:
        case RnRequest.Reqs{ctx, n, note, log}:
          {==}
    case RnState.Failed{why}:
      match t:
        case RnRequest.Reqs{ctx, n, note, log}:
          {==}

# the requests logged after evs from s and t are those t logged and one per call made
def lg.run(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, +t: RnRequest.Reqs) -> {Run.sents(RnRequest.Reqs.log(RnRequest.reqs.go(evs, cfg, s, t))) == Nat.add(Run.calls_made(evs, cfg, s), Run.sents(RnRequest.Reqs.log(t))) : Nat}:
  match evs:
    case Nil{}:
      {==}
    case +e <> +rest:
      +s2 = RnStep.step(cfg, s, e)
      +t2 = RnRequest.Reqs.step(RnState.St.ph(s), e, RnState.St.ph(s2), t)
      +b = Run.sends_one(RnState.St.ph(s), RnState.St.ph(s2))
      %Equal.sym(Nat, Nat.add(Nat.add(Run.calls_made(rest, cfg, s2), b), Run.sents(RnRequest.Reqs.log(t))), Nat.add(Run.calls_made(rest, cfg, s2), Nat.add(b, Run.sents(RnRequest.Reqs.log(t)))), lg.assoc(Run.calls_made(rest, cfg, s2), b, Run.sents(RnRequest.Reqs.log(t)))) : {Run.sents(RnRequest.Reqs.log(RnRequest.reqs.go(rest, cfg, s2, t2))) == _ : Nat}
      %lg.step(RnState.St.ph(s), e, RnState.St.ph(s2), t) : {Run.sents(RnRequest.Reqs.log(RnRequest.reqs.go(rest, cfg, s2, t2))) == Nat.add(Run.calls_made(rest, cfg, s2), _) : Nat}
      lg.run(rest, cfg, s2, t2)

def Run.run_every_call_is_logged(cfg, evs):
  %Equal.sym(Nat, Run.calls_made(evs, cfg, RnState.init(cfg)), Nat.add(Run.calls_made(evs, cfg, RnState.init(cfg)), 0n), LA.rk.add0(Run.calls_made(evs, cfg, RnState.init(cfg)))) : {Run.sents(RnRequest.Reqs.log(RnRequest.reqs(cfg, evs))) == _ : Nat}
  lg.run(evs, cfg, RnState.init(cfg), RnRequest.Reqs.init())
