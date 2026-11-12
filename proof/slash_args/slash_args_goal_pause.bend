# eukhe: the proof of LAW slash_args_goal_pause
#
# PROOF: the text is its own trim (LA.sab.trim_edge) and its lowercase is
# `pause` (LA.sab.str_eq), which `/goal` answers.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def SlashArgs.slash_args_goal_pause(t, e, k):
  LA.sab.goal_kw(t, e, "pause", k)
