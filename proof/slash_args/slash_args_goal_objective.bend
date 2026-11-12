# eukhe: the proof of LAW slash_args_goal_objective
#
# PROOF: the text is its own trim and no keyword (LA.sab.goal_plain); its
# first piece asks for no budget (LA.sab.start_plain), so the whole text
# is the objective, judged by R5 (LA.sab.obj).

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def SlashArgs.slash_args_goal_objective(t, e, k, f):
  Equal.trans(Sa.Goal, Sa.goal(t), Sa.goal.start(Sa.cut(t), t), SlashArgs.sa_verdict(t, None{}), LA.sab.goal_plain(t, e, k), Equal.trans(Sa.Goal, Sa.goal.start(Sa.cut(t), t), Sa.goal.objective(t, None{}), SlashArgs.sa_verdict(t, None{}), LA.sab.start_plain(t, f), LA.sab.obj(t, t, None{}, LA.sab.trim_edge(t, e), e)))
