# eukhe: the proof of LAW slash_args_goal_blank
#
# PROOF: a White_Space text trims to nothing (LA.sab.trim_nil), the
# status.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def SlashArgs.slash_args_goal_blank(w, b):
  %Equal.sym(String, Sa.trim(w), SNil{}, LA.sab.trim_nil(w, b)) : {Sa.goal.of(_, String.to_lower(_)) == Sa.GStatus{} : Sa.Goal}
  {==}
