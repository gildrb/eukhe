# eukhe: the proof of LAW commit_gate_seen_digest_proceeds
#
# PROOF: the shipped membership finds the digest in its place (dcq.member_at).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_gate_seen_digest_proceeds(pre, g, post, e):
  %Equal.sym(Bool, Cm.member(g, List.append(&2, String, pre, g <> post)), True{}, LC.dcq.member_at(pre, g, post)) : {Cm.gate.seen(_) == Cm.Proceed{} : Cm.Gate}
  {==}
