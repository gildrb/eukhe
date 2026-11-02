# eukhe: the proof of LAW launcher_go_exact
# By induction on the operations: each step is the rule's
# (launcher_step_exact).

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher

def Launcher.launcher_go_exact(ops, s):
  match ops:
    case Nil{}:
      {==}
    case +op <> rest:
      %Launcher.launcher_step_exact(s, op) : {La.go(rest, La.step(s, op)) == Launcher.run_spec(rest, _) : La.St}
      Launcher.launcher_go_exact(rest, La.step(s, op))
