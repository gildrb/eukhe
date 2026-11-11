# eukhe: the proof of LAW slash_args_objective_judged
#
# PROOF: the objective trims to o (LA.sab.trim_pad, LA.sab.trim_edge),
# judged by R5 (LA.sab.obj); a White_Space objective trims to nothing
# (LA.sab.trim_nil).

import Base
import ../../bend/slash_args.bend as Sa
import ../../bend/gateway_answer.bend as Ga
import ../../laws/slash_args/model.bend as SlashArgs
import ../base/staging.bend as LStg
import ./base.bend as LA

def sgo.blank(+w: String, +b: {SlashArgs.sa_blank(w) == True{} : Bool}, m: Maybe<&2, String>) -> {Sa.goal.objective(w, m) == Sa.GErr{"Goal objective must not be empty."} : Sa.Goal}:
  %Equal.sym(String, Sa.trim(w), SNil{}, LA.sab.trim_nil(w, b)) : {Sa.goal.objective.at(String.is_empty(_), Bool.not(Nat.is_le(String.length(_), 4000n)), _, m) == Sa.GErr{"Goal objective must not be empty."} : Sa.Goal}
  {==}

def SlashArgs.slash_args_objective_judged(w1, b1, o, oe, w2, b2, b):
  +x = String.append(w1, String.append(o, w2))
  (LA.sab.obj(x, o, b, Equal.trans(String, Sa.trim(x), Sa.trim(o), o, LA.sab.trim_pad(w1, b1, o, w2, b2), LA.sab.trim_edge(o, oe)), oe), sgo.blank(w1, b1, b))
