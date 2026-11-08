# eukhe: the proof of LAW kin_relation_exact
#
# PROOF: the decision is the spec's verdict (kin_refines_spec); an admitted spec verdict passed the edge it names (kr.self).

import Base
import ../../bend/kin.bend as K
import ../../spec/agents/kin.bend as KinSpec
import ../../laws/kin.bend as Kin
import ./base.bend as LK
import ./kin_refines_spec.bend as PKinRefinesSpec


def Kin.kin_relation_exact(s, t, cs, ps, r, e):
  LK.kr.self(String.eq(s, t), s, t, cs, ps, r, Equal.trans(K.Verdict, KinSpec.verdict(s, t, cs, ps), K.decide(s, t, cs, ps), K.Admit{r}, Equal.sym(K.Verdict, K.decide(s, t, cs, ps), KinSpec.verdict(s, t, cs, ps), Kin.kin_refines_spec(s, t, cs, ps)), e))
