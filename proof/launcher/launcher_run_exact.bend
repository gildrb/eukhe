# eukhe: the proof of LAW launcher_run_exact
# The start is the laws' open workers (la.open); the run from it is the
# rule's steps (launcher_go_exact).

import Base
import ../../bend/launcher.bend as La
import ../../laws/launcher.bend as Launcher
import ./base.bend as LLa

def Launcher.launcher_run_exact(bs, ops):
  %LLa.la.open(bs) : {La.go(ops, La.St{La.open(bs), 0n, False{}}) == Launcher.run_spec(ops, La.St{_, 0n, False{}}) : La.St}
  Launcher.launcher_go_exact(ops, La.St{La.open(bs), 0n, False{}})
