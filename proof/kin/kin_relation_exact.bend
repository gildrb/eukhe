# eukhe: the proof of LAW kin_relation_exact
#
# PROOF: the decision is the three-step verdict (kp.decide_eq); an admitted verdict passed the edge it names (kr.self).

import Base
import ../../bend/kin.bend as K
import ../../spec/agents/kin.bend as KinSpec
import ../../laws/kin.bend as Kin
import ./base.bend as LK


def Kin.kin_relation_exact(s, t, cs, ps, r, e):
  LK.kr.self(String.eq(s, t), s, t, cs, ps, r, Equal.trans(K.Verdict, LK.kp.verdict(s, t, cs, ps), K.decide(s, t, cs, ps), K.Admit{r}, Equal.sym(K.Verdict, K.decide(s, t, cs, ps), LK.kp.verdict(s, t, cs, ps), LK.kp.decide_eq(s, t, cs, ps)), e))
