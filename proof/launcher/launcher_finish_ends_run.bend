# eukhe: the proof of LAW launcher_finish_ends_run
#
# The step puts `finish` at worker i (LLa.la.at_here); `finish` of that
# worker computes.

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def Launcher.launcher_finish_ends_run(ws, a, i, b, c, at):
  LLa.la.at_here(~La.finish, i, ws, La.Wk{b, c}, at)
