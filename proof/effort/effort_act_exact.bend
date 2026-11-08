# eukhe: the proof of LAW effort_act_exact
# Case by case on the action, the stored level and the model
# (LA.ps.act): the clamp, fit and cycle are the laws'.

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/entry.bend as EffortEntry
import ./base.bend as LA

def EffortEntry.effort_act_exact(a, s):
  LA.ps.act(a, s)
