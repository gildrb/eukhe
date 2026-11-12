# eukhe: the proof of LAW slash_args_goal_clear
#
# PROOF: the text is its own trim (LA.sab.trim_edge) and its lowercase is
# `clear` or `stop` (LA.sab.str_eq), both of which clear the goal.

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def sgc.at(+t: String, +e: {SlashArgs.sa_edge(t) == True{} : Bool}, b: Bool, eb: {String.eq(String.to_lower(t), "clear") == b : Bool}, k: {Bool.or(b, String.eq(String.to_lower(t), "stop")) == True{} : Bool}) -> {Sa.goal(t) == Sa.GClear{} : Sa.Goal}:
  match b:
    case True{}:
      LA.sab.goal_kw(t, e, "clear", eb)
    case False{}:
      LA.sab.goal_kw(t, e, "stop", k)

def SlashArgs.slash_args_goal_clear(t, e, k):
  sgc.at(t, e, String.eq(String.to_lower(t), "clear"), {==}, k)
