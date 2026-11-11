# eukhe: the proof of LAW commit_check_clear_goes
#
# PROOF: from any index, clear files check on to Go (dcq.clear).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_check_clear_goes(n):
  LC.dcq.clear(n, 0n)
