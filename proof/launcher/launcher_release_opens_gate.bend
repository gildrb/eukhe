# eukhe: the proof of LAW launcher_release_opens_gate
#
# The step puts `release` at worker i (LLa.la.at_here); `release` of that
# worker computes.

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def Launcher.launcher_release_opens_gate(ws, a, i, b, c, at):
  LLa.la.at_here(~La.release, i, ws, La.Wk{b, c}, at)
