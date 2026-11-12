# eukhe: the proof of LAW launcher_op_keeps_serving
#
# On a serving daemon a run start, run end, quiesce or release only
# rewrites one worker; the state's stop flag and aborted count compute
# as they were. A commit is on no worker.

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def Launcher.launcher_op_keeps_serving(ws, a, op, i, on):
  match op:
    case La.Prompt{k}:
      ({==}, {==})
    case La.Finish{k}:
      ({==}, {==})
    case La.Quiesce{k}:
      ({==}, {==})
    case La.Release{k}:
      ({==}, {==})
    case La.Commit{}:
      LLa.la.none_some(Nat, i, ({Launcher.la_stopped(La.step(La.St{ws, a, False{}}, La.Commit{})) == False{} : Bool} & {Launcher.la_aborted(La.step(La.St{ws, a, False{}}, La.Commit{})) == a : Nat}), on)
