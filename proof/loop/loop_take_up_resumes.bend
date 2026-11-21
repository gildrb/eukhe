# eukhe: the proof of LAW loop_take_up_resumes
#
# PROOF: Lp.restart in a turn rebuilds the same state with Resume of its
# iteration and prompt, whatever the condition and the failed turns: it
# computes.

import Base
import ../../bend/loop.bend as Lp
import ../../spec/loop/loop.bend as S
import ../../laws/loop/model.bend as Loop

def Loop.loop_take_up_resumes(i, l, d, c, b, f, x):
  {==}
