# eukhe: the proof of LAW launcher_prompt_starts_at_open_gate
#
# The step puts `prompt` at worker i (LLa.la.at_here); `prompt` of that
# worker computes.

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def Launcher.launcher_prompt_starts_at_open_gate(ws, a, i, b, at):
  LLa.la.at_here(~La.prompt, i, ws, La.Wk{b, False{}}, at)
