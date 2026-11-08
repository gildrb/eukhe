# eukhe: the proof of LAW kin_refines_spec
#
# PROOF: the code's edge test is the spec's (kp.has), and each step of the decision is the spec's (kp.self).

import Base
import ../../bend/kin.bend as K
import ../../spec/agents/kin.bend as KinSpec
import ../../laws/kin.bend as Kin
import ./base.bend as LK


def Kin.kin_refines_spec(s, t, cs, ps):
  LK.kp.self(String.eq(s, t), s, t, cs, ps)
