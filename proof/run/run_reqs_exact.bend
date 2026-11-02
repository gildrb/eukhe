# eukhe: the proof of LAW run_reqs_exact
#
# PROOF: the requests' step is rm.reqs.step (case by case) and a state's
# phase is rm.ph; then induction on the inputs, from any state and any
# requests: the run's step is run_step_exact (rmx.step).

import Base
import ../../bend/run/request.bend as RnRequest
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/machine.bend as RunMachine
import ./run_step_exact.bend as PRunStepExact

def rqx.ph(s: RnState.St) -> {RnState.St.ph(s) == RunMachine.rm.ph(s) : RnState.Ph}:
  match s:
    case RnState.St{ph, r, c, a, n, p}:
      {==}

def rqx.reply(reply: RnState.Reply, -ctx: Nat, -n: Nat, -note: Nat, -log: List<&2, RnRequest.Sent>, -fin: RnState.Fin, -got: RnState.Got, -pa: RnState.Ph) -> {RnRequest.Reqs.step(RnState.Call{}, RnState.Go{reply, fin, got}, pa, RnRequest.Reqs{ctx, n, note, log}) == RunMachine.rm.reqs.step(RnRequest.Reqs{ctx, n, note, log}, RnState.Call{}, RnState.Go{reply, fin, got}, pa) : RnRequest.Reqs}:
  match reply:
    case RnState.Error{retryable, noted}:
      match noted:
        case True{}:
          {==}
        case False{}:
          {==}
    case RnState.Plain{}:
      {==}
    case RnState.Calls{}:
      {==}
    case RnState.Deferred{}:
      {==}
    case RnState.Overflow{cut}:
      {==}

def rqx.step(t: RnRequest.Reqs, pb: RnState.Ph, e: RnState.Ev, pa: RnState.Ph) -> {RnRequest.Reqs.step(pb, e, pa, t) == RunMachine.rm.reqs.step(t, pb, e, pa) : RnRequest.Reqs}:
  match t:
    case RnRequest.Reqs{ctx, n, note, log}:
      match pb:
        case RnState.Prepare{}:
          match pa:
            case RnState.Call{}:
              {==}
            case RnState.Prepare{}:
              {==}
            case RnState.Compact{over}:
              {==}
            case RnState.Tools{}:
              {==}
            case RnState.Answered{}:
              {==}
            case RnState.Aborted{}:
              {==}
            case RnState.Failed{why}:
              {==}
        case RnState.Call{}:
          match e:
            case RnState.Abort{}:
              {==}
            case RnState.Go{reply, fin, got}:
              rqx.reply(reply, ctx, n, note, log, fin, got, pa)
        case RnState.Compact{over}:
          match e:
            case RnState.Abort{}:
              {==}
            case RnState.Go{reply, fin, got}:
              match got:
                case RnState.Built{}:
                  {==}
                case RnState.Kept{}:
                  {==}
                case RnState.Broke{}:
                  {==}
        case RnState.Tools{}:
          match pa:
            case RnState.Prepare{}:
              {==}
            case RnState.Call{}:
              {==}
            case RnState.Compact{over}:
              {==}
            case RnState.Tools{}:
              {==}
            case RnState.Answered{}:
              {==}
            case RnState.Aborted{}:
              {==}
            case RnState.Failed{why}:
              {==}
        case RnState.Answered{}:
          {==}
        case RnState.Aborted{}:
          {==}
        case RnState.Failed{why}:
          {==}

def rqx.go(evs: List<&2, RnState.Ev>, +cfg: RnState.Cfg, +s: RnState.St, +t: RnRequest.Reqs) -> {RnRequest.reqs.go(evs, cfg, s, t) == RunMachine.rm.reqs.go(evs, cfg, s, t) : RnRequest.Reqs}:
  match evs:
    case Nil{}:
      {==}
    case +e <> rest:
      +x = RnStep.step(cfg, s, e)
      %PRunStepExact.rmx.step(cfg, s, e) : {RnRequest.reqs.go(rest, cfg, x, RnRequest.Reqs.step(RnState.St.ph(s), e, RnState.St.ph(x), t)) == RunMachine.rm.reqs.go(rest, cfg, _, RunMachine.rm.reqs.step(t, RunMachine.rm.ph(s), e, RunMachine.rm.ph(_))) : RnRequest.Reqs}
      %rqx.ph(s) : {RnRequest.reqs.go(rest, cfg, x, RnRequest.Reqs.step(RnState.St.ph(s), e, RnState.St.ph(x), t)) == RunMachine.rm.reqs.go(rest, cfg, x, RunMachine.rm.reqs.step(t, _, e, RunMachine.rm.ph(x))) : RnRequest.Reqs}
      %rqx.ph(x) : {RnRequest.reqs.go(rest, cfg, x, RnRequest.Reqs.step(RnState.St.ph(s), e, RnState.St.ph(x), t)) == RunMachine.rm.reqs.go(rest, cfg, x, RunMachine.rm.reqs.step(t, RnState.St.ph(s), e, _)) : RnRequest.Reqs}
      %rqx.step(t, RnState.St.ph(s), e, RnState.St.ph(x)) : {RnRequest.reqs.go(rest, cfg, x, RnRequest.Reqs.step(RnState.St.ph(s), e, RnState.St.ph(x), t)) == RunMachine.rm.reqs.go(rest, cfg, x, _) : RnRequest.Reqs}
      rqx.go(rest, cfg, x, RnRequest.Reqs.step(RnState.St.ph(s), e, RnState.St.ph(x), t))

def RunMachine.run_reqs_exact(cfg, evs):
  match cfg:
    case RnState.Cfg{cap, polls, retries, notes}:
      rqx.go(evs, RnState.Cfg{cap, polls, retries, notes}, RnState.St{RnState.Prepare{}, Nat.sub(cap, 1n), 1n, retries, notes, polls}, RnRequest.Reqs{0n, 1n, 0n, Nil{}})
