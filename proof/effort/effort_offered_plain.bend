# eukhe: the proof of LAW effort_offered_plain

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort.bend as Effort

# The laws
# --------

def pe.effort_offered_plain(+map: Ef.LvMap) -> {Ef.offered(Ef.Mdl{False{}, map}) == [Ef.Off{}] : List<&2, Ef.Lv>}:
  {==}

# (S10) Reasoning depth

def Effort.effort_offered_plain(map):
  pe.effort_offered_plain(map)
