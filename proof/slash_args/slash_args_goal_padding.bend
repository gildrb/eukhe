# eukhe: the proof of LAW slash_args_goal_padding
#
# PROOF: `/goal` reads its args trimmed; White_Space at both ends does not
# change the trimmed text (LA.sab.trim_pad).

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def SlashArgs.slash_args_goal_padding(w1, b1, s, w2, b2):
  %Equal.sym(String, Sa.trim(String.append(w1, String.append(s, w2))), Sa.trim(s), LA.sab.trim_pad(w1, b1, s, w2, b2)) : {Sa.goal.of(_, String.to_lower(_)) == Sa.goal(s) : Sa.Goal}
  {==}
