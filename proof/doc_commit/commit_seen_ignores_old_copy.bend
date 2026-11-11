# eukhe: the proof of LAW commit_seen_ignores_old_copy
#
# PROOF: unsee drops the copy of d wherever it is (dcq.unsee_drop).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_seen_ignores_old_copy(d, pre, post):
  Equal.cong(List<&2, String>, List<&2, String>, z => List.take(&2, String, d <> z, 8n), Cm.unsee(d, List.append(&2, String, pre, d <> post)), Cm.unsee(d, List.append(&2, String, pre, post)), LC.dcq.unsee_drop(d, pre, post))
