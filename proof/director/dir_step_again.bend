# eukhe: the proof of LAW dir_step_again

import Base
import ../../bend/director.bend as Dr
import ../../laws/director.bend as Director
import ./base.bend as LA

def Director.dir_step_again(m, a, k, c, b, va, vr, cap, one, pass):
  LA.pd.step_at(1n+m, a, Dr.Layer{k, 1n+c}, b, va, Dr.Again{}, vr, cap, one, pass)
