# eukhe: the proof of LAW kin_no_cross_tree
#
# PROOF: the decision admits exactly when the spec admits (kin_admit_iff); the links of A ++ B are A's then B's (kb.links_app, A's columns of one length), and no link of A reaches the target (kb.no_parent, kb.no_child) nor any of B leaves or reaches the sender, so neither edge holds (kb.no_edge).

import Base
import ../../bend/kin.bend as K
import ../../spec/agents/kin.bend as KinSpec
import ../../laws/kin.bend as Kin
import ./base.bend as LK
import ./kin_admit_iff.bend as PKinAdmitIff
import ../base/staging.bend as LStg


def Kin.kin_no_cross_tree(s, t, ca, pa, cb, pb, hl, h1, h2, h3, h4):
  +l = hl
  +cs = List.append(&2, String, ca, cb)
  +ps = List.append(&2, String, pa, pb)
  %Equal.sym(Bool, Kin.kin_admitted(K.decide(s, t, cs, ps)), KinSpec.admits(s, t, cs, ps), Kin.kin_admit_iff(s, t, cs, ps)) : {_ == False{} : Bool}
  %Equal.sym(Bool, KinSpec.has_edge(cs, ps, s, t), False{}, LK.kb.no_edge(ca, pa, cb, pb, s, t, l, LK.kb.no_parent(ca, pa, s, t, h4), LK.kb.no_child(cb, pb, s, t, h1))) : {Bool.and(Bool.not(String.eq(s, t)), Bool.or(_, KinSpec.has_edge(cs, ps, t, s))) == False{} : Bool}
  %Equal.sym(Bool, KinSpec.has_edge(cs, ps, t, s), False{}, LK.kb.no_edge(ca, pa, cb, pb, t, s, l, LK.kb.no_child(ca, pa, t, s, h3), LK.kb.no_parent(cb, pb, t, s, h2))) : {Bool.and(Bool.not(String.eq(s, t)), Bool.or(False{}, _)) == False{} : Bool}
  LStg.stg.and_false(Bool.not(String.eq(s, t)))
