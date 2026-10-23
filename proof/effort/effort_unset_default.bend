# eukhe: the proof of LAW effort_unset_default

import Base
import ../../bend/effort.bend as Ef
import ../../LAWS.bend as Laws

def pe.effort_unset_default(+mo: Maybe<&2, Ef.Mdl>) -> {Ef.shown(Ef.Sess{mo, None{}}) == Ef.Default{} : Ef.Shown}:
  {==}

def Laws.effort_unset_default(mo):
  pe.effort_unset_default(mo)
