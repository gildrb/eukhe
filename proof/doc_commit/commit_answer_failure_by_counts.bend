# eukhe: the proof of LAW commit_answer_failure_by_counts
#
# PROOF: the reply is an error exactly on its test (dcq.isf); some publish failed exactly when the failed count is not 0 (dcq.failed), none landed exactly when the landed count is 0 (dcq.landed).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_answer_failure_by_counts(fs):
  Equal.trans(Bool, DocCommitChoices.is_failure(Cm.answer(fs)), Bool.and(Cm.any.failed(fs), Bool.not(Cm.any.landed(fs))), Bool.and(Nat.is_gt(DocCommitChoices.nfailed(fs), 0n), Nat.is_eq(DocCommitChoices.nlanded(fs), 0n)), LC.dcq.isf(Bool.and(Cm.any.failed(fs), Bool.not(Cm.any.landed(fs))), fs), Equal.trans(Bool, Bool.and(Cm.any.failed(fs), Bool.not(Cm.any.landed(fs))), Bool.and(Nat.is_gt(DocCommitChoices.nfailed(fs), 0n), Bool.not(Cm.any.landed(fs))), Bool.and(Nat.is_gt(DocCommitChoices.nfailed(fs), 0n), Nat.is_eq(DocCommitChoices.nlanded(fs), 0n)), Equal.cong(Bool, Bool, z => Bool.and(z, Bool.not(Cm.any.landed(fs))), Cm.any.failed(fs), Nat.is_gt(DocCommitChoices.nfailed(fs), 0n), LC.dcq.failed(fs)), Equal.cong(Bool, Bool, z => Bool.and(Nat.is_gt(DocCommitChoices.nfailed(fs), 0n), z), Bool.not(Cm.any.landed(fs)), Nat.is_eq(DocCommitChoices.nlanded(fs), 0n), LC.dcq.landed(fs))))
