# eukhe: the proof of LAW goal_text_prompt_spec
#
# PROOF: each prompt's pieces are the spec's (gtb.objective, gtb.status_name, gtb.budget_text, gtb.left_text; the tokens left by induction on the digits, gtb.sub), and the templates are alike (gtb.prompt).

import Base
import ../../bend/goal_text.bend as Gt
import ../../bend/ffi_goal_text.bend as FGt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/goal_text.bend as GoalText
import ./base.bend as LA

def GoalText.goal_text_prompt_spec(k, g):
  LA.gtb.prompt(k, g)
