# eukhe: the proof of LAW goal_text_left_spec
#
# PROOF: both numbers canonical alike, the subtraction alike by induction on
# the digits (gtb.left, gtb.sub).

import Base
import ../../bend/goal_text.bend as Gt
import ../../bend/ffi_goal_text.bend as FGt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/goal_text.bend as GoalText
import ./base.bend as LA

def GoalText.goal_text_left_spec(b, u):
  LA.gtb.left(b, u)
