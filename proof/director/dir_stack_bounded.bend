# eukhe: the proof of LAW dir_stack_bounded

import Base
import ../../laws/director.bend as Director
import ./base.bend as LA

# (S5) The Director stack

def Director.dir_stack_bounded(s, vs, cap, fits):
  LA.pd.dir_stack_bounded(s, vs, cap, fits)
