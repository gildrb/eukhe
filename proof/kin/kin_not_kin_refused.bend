# eukhe: the proof of LAW kin_not_kin_refused
#
# PROOF: the sender is not the target (other), so the spec not admitting (no) means no edge either way (kb.or_false_l, kb.or_false_r); the decision is the three-step verdict (kp.decide_eq), which then falls through the parent and child steps to the refusal.

import Base
import ../../bend/kin.bend as K
import ../../spec/agents/kin.bend as KinSpec
import ../../laws/kin.bend as Kin
import ./base.bend as LK


def Kin.kin_not_kin_refused(s, t, cs, ps, other, no):
  +o = other
  +h = Equal.trans(Bool, Bool.or(KinSpec.has_edge(cs, ps, s, t), KinSpec.has_edge(cs, ps, t, s)), Bool.and(Bool.not(String.eq(s, t)), Bool.or(KinSpec.has_edge(cs, ps, s, t), KinSpec.has_edge(cs, ps, t, s))), False{}, Equal.cong(Bool, Bool, z => Bool.and(Bool.not(z), Bool.or(KinSpec.has_edge(cs, ps, s, t), KinSpec.has_edge(cs, ps, t, s))), False{}, String.eq(s, t), Equal.sym(Bool, String.eq(s, t), False{}, o)), no)
  %Equal.sym(K.Verdict, K.decide(s, t, cs, ps), LK.kp.verdict(s, t, cs, ps), LK.kp.decide_eq(s, t, cs, ps)) : {_ == K.Refuse{K.NotKin{}} : K.Verdict}
  %Equal.sym(Bool, String.eq(s, t), False{}, o) : {LK.kp.verdict.self(_, s, t, cs, ps) == K.Refuse{K.NotKin{}} : K.Verdict}
  %Equal.sym(Bool, KinSpec.has_edge(cs, ps, s, t), False{}, LK.kb.or_false_l(KinSpec.has_edge(cs, ps, s, t), KinSpec.has_edge(cs, ps, t, s), h)) : {LK.kp.verdict.parent(_, s, t, cs, ps) == K.Refuse{K.NotKin{}} : K.Verdict}
  %Equal.sym(Bool, KinSpec.has_edge(cs, ps, t, s), False{}, LK.kb.or_false_r(KinSpec.has_edge(cs, ps, s, t), KinSpec.has_edge(cs, ps, t, s), h)) : {LK.kp.verdict.child(_) == K.Refuse{K.NotKin{}} : K.Verdict}
  {==}
