# eukhe: the proof of LAW dir_stack_bounded

import Base
import ../../LAWS.bend as Laws
import ./base.bend as LA

# (S5) The Director stack

def Laws.dir_stack_bounded(s, vs, cap, fits):
  LA.pd.dir_stack_bounded(s, vs, cap, fits)
