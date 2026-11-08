# eukhe: the proof of LAW run_step_exact
#
# PROOF: case by case, one helper per phase (each matches its own inputs,
# the configuration first, so both steps compute to the same state).

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/machine.bend as RunMachine

def rmx.prepare(cfg: RnState.Cfg, reply: RnState.Reply, r: Nat, c: Nat, a: Nat, n: Nat) -> {RnStep.prepare(cfg, reply, r, c, a, n) == RunMachine.rm.prepare(cfg, reply, r, c, a, n) : RnState.St}:
  match cfg:
    case RnState.Cfg{cap, polls, retries, notes}:
      match reply:
        case RnState.Overflow{cut}:
          match cut:
            case True{}:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  {==}
            case False{}:
              {==}
        case RnState.Plain{}:
          {==}
        case RnState.Calls{}:
          {==}
        case RnState.Deferred{}:
          {==}
        case RnState.Error{retryable, noted}:
          {==}

def rmx.call(cfg: RnState.Cfg, reply: RnState.Reply, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> {RnStep.call(cfg, reply, r, c, a, n, p) == RunMachine.rm.call(cfg, reply, r, c, a, n, p) : RnState.St}:
  match cfg:
    case RnState.Cfg{cap, polls, retries, notes}:
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
          match retryable:
            case True{}:
              match noted:
                case True{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n+m:
                      {==}
                case False{}:
                  match a:
                    case 0n:
                      {==}
                    case 1n+b:
                      {==}
            case False{}:
              match noted:
                case True{}:
                  match n:
                    case 0n:
                      {==}
                    case 1n+m:
                      {==}
                case False{}:
                  {==}
        case RnState.Overflow{cut}:
          match cut:
            case True{}:
              match c:
                case 0n:
                  {==}
                case 1n+d:
                  {==}
            case False{}:
              {==}

def rmx.compact(cfg: RnState.Cfg, over: Bool, got: RnState.Got, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> {RnStep.compact(cfg, over, got, r, c, a, n, p) == RunMachine.rm.compact(cfg, got, over, r, c, a, n, p) : RnState.St}:
  match cfg:
    case RnState.Cfg{cap, polls, retries, notes}:
      match over:
        case True{}:
          match got:
            case RnState.Built{}:
              {==}
            case RnState.Kept{}:
              {==}
            case RnState.Broke{}:
              {==}
        case False{}:
          match got:
            case RnState.Built{}:
              {==}
            case RnState.Kept{}:
              {==}
            case RnState.Broke{}:
              {==}

def rmx.tools(cfg: RnState.Cfg, fin: RnState.Fin, r: Nat, c: Nat, a: Nat, n: Nat, p: Nat) -> {RnStep.tools(cfg, fin, r, c, a, n, p) == RunMachine.rm.tools(cfg, fin, r, c, a, n, p) : RnState.St}:
  match cfg:
    case RnState.Cfg{cap, polls, retries, notes}:
      match fin:
        case RnState.Stops{}:
          {==}
        case RnState.Goes{}:
          match r:
            case 0n:
              {==}
            case 1n+s:
              {==}
        case RnState.Resets{}:
          match r:
            case 0n:
              {==}
            case 1n+s:
              {==}

def rmx.step(cfg: RnState.Cfg, s: RnState.St, e: RnState.Ev) -> {RnStep.step(cfg, s, e) == RunMachine.rm.step(cfg, s, e) : RnState.St}:
  match s:
    case RnState.St{ph, r, c, a, n, p}:
      match ph:
        case RnState.Answered{}:
          {==}
        case RnState.Aborted{}:
          {==}
        case RnState.Failed{why}:
          {==}
        case RnState.Prepare{}:
          match e:
            case RnState.Abort{}:
              {==}
            case RnState.Go{reply, fin, got}:
              rmx.prepare(cfg, reply, r, c, a, n)
        case RnState.Call{}:
          match e:
            case RnState.Abort{}:
              {==}
            case RnState.Go{reply, fin, got}:
              rmx.call(cfg, reply, r, c, a, n, p)
        case RnState.Compact{over}:
          match e:
            case RnState.Abort{}:
              {==}
            case RnState.Go{reply, fin, got}:
              rmx.compact(cfg, over, got, r, c, a, n, p)
        case RnState.Tools{}:
          match e:
            case RnState.Abort{}:
              {==}
            case RnState.Go{reply, fin, got}:
              rmx.tools(cfg, fin, r, c, a, n, p)

def RunMachine.run_step_exact(cfg, s, e):
  rmx.step(cfg, s, e)
