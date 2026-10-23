# eukhe: the proof of LAW dash_current_open_pairs

import Base
import ../../bend/dash.bend as Da
import ../../LAWS.bend as Laws
import ./base.bend as LA

def pa.current_open_pairs(+s: Da.St, +c: Nat) -> {Da.out(s, Da.Open{c, Some{Da.St.cur(s)}}) == Da.Paired{c} : Da.Out}:
  %LA.pa.eq_refl(Da.St.cur(s)) : {Da.open.out(c, _) == Da.Paired{c} : Da.Out}
  {==}

def Laws.dash_current_open_pairs(s, c):
  pa.current_open_pairs(s, c)
