# eukhe: the proof of LAW run_live_never_waits

import Base
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run/model.bend as Run
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/nat.bend as LLogicNat
import ../base/nat.bend as LNat
import ../base/run.bend as LRun

# m is never k + 1 + m
def no_self_fall(+k: Nat, m: Nat, e: {m == Nat.add(k, 1n+m) : Nat}) -> Empty:
  match m:
    case 0n:
      LLogicLogic.pf.succ_ne_zero(Empty, Nat.add(k, 0n), Equal.sym(Nat, 0n, 1n+Nat.add(k, 0n), Equal.trans(Nat, 0n, Nat.add(k, 1n+0n), 1n+Nat.add(k, 0n), e, LNat.add_succ(k, 0n))))
    case 1n+q:
      no_self_fall(k, q, LLogicNat.succ_inj(q, Nat.add(k, 1n+q), Equal.trans(Nat, 1n+q, Nat.add(k, 1n+1n+q), 1n+Nat.add(k, 1n+q), e, LNat.add_succ(k, 1n+q))))

# a live run's measure M falls on every input (LRun.dec), so the step that
# would leave the run where it was would make M(s) = k + 1 + M(s)
def Run.run_live_never_waits(cfg, s, live, e):
  eq => no_self_fall(LLogicNat.K(cfg, s, e), LLogicNat.M(cfg, s),
    Equal.trans(Nat, LLogicNat.M(cfg, s), Nat.add(LLogicNat.K(cfg, s, e), 1n+LLogicNat.M(cfg, RnStep.step(cfg, s, e))), Nat.add(LLogicNat.K(cfg, s, e), 1n+LLogicNat.M(cfg, s)),
      LRun.dec(cfg, s, e, live),
      Equal.cong(RnState.St, Nat, t => Nat.add(LLogicNat.K(cfg, s, e), 1n+LLogicNat.M(cfg, t)), RnStep.step(cfg, s, e), s, eq)))
