# eukhe: the proof of LAW commit_gate_creates_on_seen
#
# PROOF: it computes.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_gate_creates_on_seen(s):
  {==}
