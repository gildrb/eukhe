# eukhe: the proof of LAW commit_answer_note_in_place
#
# PROOF: the notes are one report a file (dcq.notes); the report in a file's place is the report of its fate (dcq.rep_at), its own note (dcq.own).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_answer_note_in_place(pre, f, post, x, own, ok):
  %Equal.sym(List<&2, Cm.Note>, DocCommitChoices.notes_of(Cm.answer(List.append(&2, Cm.Fate, pre, f <> post))), Cm.reports(List.append(&2, Cm.Fate, pre, f <> post), Cm.first.failed(List.append(&2, Cm.Fate, pre, f <> post), 0n)), LC.dcq.notes(List.append(&2, Cm.Fate, pre, f <> post), ok)) : {List.get(&2, Cm.Note, _, List.length(&2, Cm.Fate, pre)) == Some{x} : Maybe<&2, Cm.Note>}
  Equal.trans(Maybe<&2, Cm.Note>, List.get(&2, Cm.Note, Cm.reports(List.append(&2, Cm.Fate, pre, f <> post), Cm.first.failed(List.append(&2, Cm.Fate, pre, f <> post), 0n)), List.length(&2, Cm.Fate, pre)), Some{Cm.report.of(Cm.first.failed(List.append(&2, Cm.Fate, pre, f <> post), 0n), f)}, Some{x}, LC.dcq.rep_at(pre, f, post, Cm.first.failed(List.append(&2, Cm.Fate, pre, f <> post), 0n)), LC.dcq.own(f, Cm.first.failed(List.append(&2, Cm.Fate, pre, f <> post), 0n), x, own))
