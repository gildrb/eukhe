# eukhe: the proof of LAW rec_quit_fails

import Base
import ../../bend/run/recovery.bend as RnRecovery
import ../../bend/run/state.bend as RnState
import ../../bend/run/step.bend as RnStep
import ../../laws/run.bend as Run

def quit_fails(+cfg: RnState.Cfg, -pass: RnState.Reply, +r: Nat, +c: Nat, +a: Nat, +n: Nat, +p: Nat) -> {RnStep.call(cfg, RnRecovery.Act.reply(RnRecovery.Quit{}, pass), r, c, a, n, p) == RnState.St{RnState.Failed{RnState.Model{}}, r, c, a, n, p} : RnState.St}:
  {==}

def Run.rec_quit_fails(cfg, pass, r, c, a, n, p):
  quit_fails(cfg, pass, r, c, a, n, p)
