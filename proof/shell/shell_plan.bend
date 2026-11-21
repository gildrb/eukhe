# eukhe: the proof of LAW shell_plan
#
# PROOF: a verdict is a refusal exactly when some part writes an own path
# (PShellVerdictConcat.svc.refused_of), which is the planned step's flag.

import Base
import ../../bend/tools.bend as Tl
import ../../laws/shell.bend as Shell
import ./shell_verdict_concat.bend as PShellVerdictConcat

def Shell.shell_plan(i, ps):
  +m = Tl.pieces.mine(ps)
  %Equal.sym(Bool, Shell.refused(Tl.verdict.of(m)), m, PShellVerdictConcat.svc.refused_of(m)) : {Tl.Planned{i, Tl.pieces.effs(ps), m} == Tl.Planned{i, Tl.pieces.effs(ps), _} : Tl.Planned}
  {==}
