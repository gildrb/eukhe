# eukhe: the proof of LAW effort_unset_default

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort.bend as Effort

def pe.effort_unset_default(+mo: Maybe<&2, Ef.Mdl>) -> {Ef.shown(Ef.Sess{mo, None{}}) == Ef.Default{} : Ef.Shown}:
  {==}

def Effort.effort_unset_default(mo):
  pe.effort_unset_default(mo)
