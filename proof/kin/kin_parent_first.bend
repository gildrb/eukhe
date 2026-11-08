# eukhe: the proof of LAW kin_parent_first
#
# PROOF: the decision is the three-step verdict (kp.decide_eq); the sender is not the target (other) and the edge from it to the target holds (up), so the parent step admits.

import Base
import ../../bend/kin.bend as K
import ../../spec/agents/kin.bend as KinSpec
import ../../laws/kin.bend as Kin
import ./base.bend as LK


def Kin.kin_parent_first(s, t, cs, ps, other, up):
  %Equal.sym(K.Verdict, K.decide(s, t, cs, ps), LK.kp.verdict(s, t, cs, ps), LK.kp.decide_eq(s, t, cs, ps)) : {_ == K.Admit{K.Parent{}} : K.Verdict}
  %Equal.sym(Bool, String.eq(s, t), False{}, other) : {LK.kp.verdict.self(_, s, t, cs, ps) == K.Admit{K.Parent{}} : K.Verdict}
  %Equal.sym(Bool, KinSpec.has_edge(cs, ps, s, t), True{}, up) : {LK.kp.verdict.parent(_, s, t, cs, ps) == K.Admit{K.Parent{}} : K.Verdict}
  {==}
