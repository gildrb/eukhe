# eukhe: the proof of LAW commit_answer_one_note_each
#
# PROOF: the notes of a reply that is not an error are one report a file (dcq.notes, dcq.reports_len).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_answer_one_note_each(fs, ok):
  Equal.trans(Nat, List.length(&2, Cm.Note, DocCommitChoices.notes_of(Cm.answer(fs))), List.length(&2, Cm.Note, Cm.reports(fs, Cm.first.failed(fs, 0n))), List.length(&2, Cm.Fate, fs), Equal.cong(List<&2, Cm.Note>, Nat, z => List.length(&2, Cm.Note, z), DocCommitChoices.notes_of(Cm.answer(fs)), Cm.reports(fs, Cm.first.failed(fs, 0n)), LC.dcq.notes(fs, ok)), LC.dcq.reports_len(fs, Cm.first.failed(fs, 0n)))
