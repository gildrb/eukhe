# eukhe: the proof of LAW commit_seen_fresh
#
# PROOF: unsee keeps a list with no copy of d (dcq.unsee_fresh); taking 8 of d and it computes.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_seen_fresh(d, s, new):
  %Equal.sym(List<&2, String>, Cm.unsee(d, s), s, LC.dcq.unsee_fresh(d, s, new)) : {List.take(&2, String, d <> _, 8n) == d <> List.take(&2, String, s, 7n) : List<&2, String>}
  {==}
