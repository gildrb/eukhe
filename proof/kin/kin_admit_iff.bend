# eukhe: the proof of LAW kin_admit_iff
#
# PROOF: the decision is the spec's verdict (kin_refines_spec), which admits exactly when the sender is not the target and an edge links them either way (ka.self).

import Base
import ../../bend/kin.bend as K
import ../../spec/agents/kin.bend as KinSpec
import ../../laws/kin.bend as Kin
import ./base.bend as LK
import ./kin_refines_spec.bend as PKinRefinesSpec


def Kin.kin_admit_iff(s, t, cs, ps):
  %Equal.sym(K.Verdict, K.decide(s, t, cs, ps), KinSpec.verdict(s, t, cs, ps), Kin.kin_refines_spec(s, t, cs, ps)) : {Kin.kin_admitted(_) == KinSpec.admits(s, t, cs, ps) : Bool}
  LK.ka.self(String.eq(s, t), s, t, cs, ps)
