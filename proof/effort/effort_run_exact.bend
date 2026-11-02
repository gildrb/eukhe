# eukhe: the proof of LAW effort_run_exact
# By induction on the actions: each action is es.act's (LA.ps.act).

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort.bend as Effort
import ./base.bend as LA

def psr.run(acts: List<&2, Ef.Act>, +s: Ef.Sess) -> {Ef.run(acts, s) == Effort.es.acts(acts, s) : Ef.Sess}:
  match acts:
    case Nil{}:
      {==}
    case +a <> rest:
      %LA.ps.act(a, s) : {Ef.run(rest, Ef.act(a, s)) == Effort.es.acts(rest, _) : Ef.Sess}
      psr.run(rest, Ef.act(a, s))

def Effort.effort_run_exact(acts, s):
  psr.run(acts, s)
