# eukhe: the proof of LAW kin_no_self
#
# PROOF: String.eq is reflexive (clm.str_refl_sym), so the decision takes its first step: the self refusal.

import Base
import ../../bend/kin.bend as K
import ../../spec/agents/kin.bend as KinSpec
import ../../laws/kin.bend as Kin
import ./base.bend as LK
import ../call_lift/base/string.bend as LCS


def Kin.kin_no_self(s, cs, ps):
  %LCS.clm.str_refl_sym(s) : {K.decide.self(_, s, s, cs, ps) == K.Refuse{K.SelfMessage{}} : K.Verdict}
  {==}
