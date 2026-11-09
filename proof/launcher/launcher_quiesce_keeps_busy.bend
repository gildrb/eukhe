# eukhe: the proof of LAW launcher_quiesce_keeps_busy
#
# The step puts `quiesce` at worker i (LLa.la.at_here); `quiesce` of that
# worker computes.

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def Launcher.launcher_quiesce_keeps_busy(ws, a, i, c, at):
  LLa.la.at_here(~La.quiesce, i, ws, La.Wk{True{}, c}, at)
