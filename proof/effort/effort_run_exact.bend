# eukhe: the proof of LAW effort_run_exact
# By induction on the actions: each action is es.act's (LA.ps.act).

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/entry.bend as EffortEntry
import ./base.bend as LA

def psr.run(acts: List<&2, Ef.Act>, +s: Ef.Sess) -> {Ef.run(acts, s) == EffortEntry.es.acts(acts, s) : Ef.Sess}:
  match acts:
    case Nil{}:
      {==}
    case +a <> rest:
      %LA.ps.act(a, s) : {Ef.run(rest, Ef.act(a, s)) == EffortEntry.es.acts(rest, _) : Ef.Sess}
      psr.run(rest, Ef.act(a, s))

def EffortEntry.effort_run_exact(acts, s):
  psr.run(acts, s)
