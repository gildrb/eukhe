# eukhe: the proof of LAW commit_answer_partial_by_counts
#
# PROOF: a reply that is not an error carries unwritten (dcq.partial_go), true exactly when the unwritten count is not 0 (dcq.unwritten).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_answer_partial_by_counts(fs, ok):
  Equal.trans(Bool, DocCommitChoices.partial_of(Cm.answer(fs)), Cm.unwritten(fs), Nat.is_gt(DocCommitChoices.nunwritten(fs), 0n), LC.dcq.partial_go(Bool.and(Cm.any.failed(fs), Bool.not(Cm.any.landed(fs))), fs, ok), LC.dcq.unwritten(fs))
