# eukhe: the proof of LAW commit_answer_skip_without_failure
#
# PROOF: with no failure the reply is not an error (dcq.no_fail); its notes are one report a file (dcq.notes), and the untried file's report names the first failure, past the last file (dcq.ff_all).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def dcf.swf(+pre: List<&2, Cm.Fate>, +post: List<&2, Cm.Fate>, +clean: {Nat.is_eq(DocCommitChoices.nfailed(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post)), 0n) == True{} : Bool}) -> {List.get(&2, Cm.Note, DocCommitChoices.notes_of(Cm.answer(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post))), List.length(&2, Cm.Fate, pre)) == Some{Cm.Skipped{List.length(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post))}} : Maybe<&2, Cm.Note>}:
  %Equal.sym(List<&2, Cm.Note>, DocCommitChoices.notes_of(Cm.answer(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post))), Cm.reports(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post), Cm.first.failed(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post), 0n)), LC.dcq.notes(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post), LC.dcq.no_fail(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post), clean))) : {List.get(&2, Cm.Note, _, List.length(&2, Cm.Fate, pre)) == Some{Cm.Skipped{List.length(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post))}} : Maybe<&2, Cm.Note>}
  Equal.trans(Maybe<&2, Cm.Note>, List.get(&2, Cm.Note, Cm.reports(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post), Cm.first.failed(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post), 0n)), List.length(&2, Cm.Fate, pre)), Some{Cm.Skipped{Cm.first.failed(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post), 0n)}}, Some{Cm.Skipped{List.length(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post))}}, LC.dcq.rep_at(pre, Cm.Untried{}, post, Cm.first.failed(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post), 0n)), Equal.cong(Nat, Maybe<&2, Cm.Note>, z => Some{Cm.Skipped{z}}, Cm.first.failed(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post), 0n), List.length(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post)), Equal.trans(Nat, Cm.first.failed(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post), 0n), Nat.add(List.length(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post)), 0n), List.length(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post)), LC.dcq.ff_all(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post), 0n, clean), LA.dcl.add_zero(List.length(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post))))))

def dcf.swf_all(+pre: List<&2, Cm.Fate>, +post: List<&2, Cm.Fate>, +clean: {Nat.is_eq(DocCommitChoices.nfailed(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post)), 0n) == True{} : Bool}) -> {DocCommitChoices.is_failure(Cm.answer(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post))) == False{} : Bool} & {List.get(&2, Cm.Note, DocCommitChoices.notes_of(Cm.answer(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post))), List.length(&2, Cm.Fate, pre)) == Some{Cm.Skipped{List.length(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post))}} : Maybe<&2, Cm.Note>}:
  (LC.dcq.no_fail(List.append(&2, Cm.Fate, pre, Cm.Untried{} <> post), clean), dcf.swf(pre, post, clean))

def DocCommitChoices.commit_answer_skip_without_failure(pre, post, clean):
  dcf.swf_all(pre, post, clean)
