# eukhe: the proof of LAW run_step_counts_rounds_down
#
# PROOF: case by case on the phase and the input: only a round's end that no control stops takes the rounds left down, by one, to none at least.

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/model.bend as Run

# preparation, a reply and a compaction's end leave the rounds left
def sr.prepare(+cfg: RnState.Cfg, reply: RnState.Reply, +r: Nat, c: Nat, +a: Nat, +n: Nat) -> {RnState.St.r(RnStep.prepare(cfg, reply, r, c, a, n)) == r : Nat}:
  match reply:
    case RnState.Overflow{cut}:
      match cut c:
        case True{} 1n+d:
          {==}
        case True{} 0n:
          {==}
        case False{} c:
          {==}
    case RnState.Plain{}:
      {==}
    case RnState.Calls{}:
      {==}
    case RnState.Deferred{}:
      {==}
    case RnState.Error{retryable, noted}:
      {==}

def sr.call(+cfg: RnState.Cfg, reply: RnState.Reply, +r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> {RnState.St.r(RnStep.call(cfg, reply, r, c, a, n, p)) == r : Nat}:
  match reply:
    case RnState.Plain{}:
      {==}
    case RnState.Calls{}:
      {==}
    case RnState.Deferred{}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case RnState.Error{retryable, noted}:
      match retryable noted:
        case retryable True{}:
          match n:
            case 0n:
              {==}
            case 1n+m:
              {==}
        case True{} False{}:
          match a:
            case 1n+b:
              {==}
            case 0n:
              {==}
        case False{} False{}:
          {==}
    case RnState.Overflow{cut}:
      match cut c:
        case True{} 1n+d:
          {==}
        case True{} 0n:
          {==}
        case False{} c:
          {==}

def sr.compact(+cfg: RnState.Cfg, over: Bool, got: RnState.Got, +r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> {RnState.St.r(RnStep.compact(cfg, over, got, r, c, a, n, p)) == r : Nat}:
  match over got:
    case True{} RnState.Built{}:
      {==}
    case True{} RnState.Kept{}:
      {==}
    case True{} RnState.Broke{}:
      {==}
    case False{} RnState.Built{}:
      {==}
    case False{} RnState.Kept{}:
      {==}
    case False{} RnState.Broke{}:
      {==}

# a round's end spends a round unless a control stops it
def sr.tools(+cfg: RnState.Cfg, fin: RnState.Fin, -reply: RnState.Reply, -got: RnState.Got, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> {RnState.St.r(RnStep.tools(cfg, fin, r, c, a, n, p)) == Run.spend(Run.counted_round(RnState.Tools{}, RnState.Go{reply, fin, got}), r) : Nat}:
  match fin:
    case RnState.Stops{}:
      {==}
    case RnState.Goes{}:
      match r:
        case 0n:
          {==}
        case 1n+q:
          {==}
    case RnState.Resets{}:
      match r:
        case 0n:
          {==}
        case 1n+q:
          {==}

def Run.run_step_counts_rounds_down(cfg, s, e):
  match s:
    case RnState.St{ph, r, c, a, n, p}:
      match ph:
        case RnState.Prepare{}:
          match e:
            case RnState.Abort{}:
              {==}
            case RnState.Go{reply, fin, got}:
              sr.prepare(cfg, reply, r, c, a, n)
        case RnState.Call{}:
          match e:
            case RnState.Abort{}:
              {==}
            case RnState.Go{reply, fin, got}:
              sr.call(cfg, reply, r, c, a, n, p)
        case RnState.Compact{over}:
          match e:
            case RnState.Abort{}:
              {==}
            case RnState.Go{reply, fin, got}:
              sr.compact(cfg, over, got, r, c, a, n, p)
        case RnState.Tools{}:
          match e:
            case RnState.Abort{}:
              {==}
            case RnState.Go{reply, fin, got}:
              sr.tools(cfg, fin, reply, got, r, c, a, n, p)
        case RnState.Answered{}:
          {==}
        case RnState.Aborted{}:
          {==}
        case RnState.Failed{why}:
          {==}
