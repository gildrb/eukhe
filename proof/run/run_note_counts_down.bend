# eukhe: the proof of LAW run_note_counts_down

import Base
import ../../bend/run/decision.bend as RnDecision
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run
import ./base.bend as LA

def rk.npred(+cfg: RnState.Cfg, +r: Nat, +c: Nat, +a: Nat, +p: Nat, +m: Nat, +x: Nat) -> {RnState.St.n(RnStep.note(cfg, r, c, a, Nat.sub(m, x), p)) == Nat.sub(m, 1n+x) : Nat}:
  match m x:
    case 0n x:
      {==}
    case 1n+v 0n:
      LA.rk.sub0(v)
    case 1n+v 1n+y:
      rk.npred(cfg, r, c, a, p, v, y)

def rk.run_note_counts_down(+l: RnDecision.Lim, +t: RnDecision.At, +r: Nat, +c: Nat, +p: Nat) -> {RnState.St.n(RnStep.note(RnDecision.Lim.cfg(l), r, c, RnDecision.At.a(l, t), RnDecision.At.n(l, t), p)) == RnDecision.At.n(l, Run.rust.noted_next(t)) : Nat}:
  match l:
    case RnDecision.Lim{+rounds, +wait, +retries, +most}:
      match t:
        case RnDecision.At{+attempt, +notes, +waited, +compacted}:
          rk.npred(RnState.Cfg{rounds, wait, retries, most}, r, c, Nat.sub(retries, Nat.sub(Nat.sub(attempt, 1n), notes)), p, most, notes)

def Run.run_note_counts_down(l, t, r, c, p):
  rk.run_note_counts_down(l, t, r, c, p)
