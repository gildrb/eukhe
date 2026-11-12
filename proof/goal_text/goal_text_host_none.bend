# eukhe: the proof of LAW goal_text_host_none
#
# PROOF: no objective computes to none; an idle goal computes to none for either objective.

import Base
import ../../bend/goal_text.bend as Gt
import ../../laws/goal_text.bend as GoalText
import ./base/text.bend as LT

def gtn.idle(o: Maybe<&2, String>, -b: Maybe<&2, String>, -u: String, -t: String, -ask: Bool) -> {Gt.host(Gt.Goal{Gt.SIdle{}, o, b, u, t}, ask) == None{} : Maybe<&2, Gt.Host>}:
  match o:
    case None{}:
      {==}
    case Some{x}:
      {==}

def GoalText.goal_text_host_none(s, o, b, u, t, ask):
  ({==}, gtn.idle(o, b, u, t, ask))
