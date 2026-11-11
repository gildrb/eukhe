# eukhe: the proof of LAW commit_answer_skip_names_first_failure
#
# PROOF: the notes are one report a file (dcq.notes); the untried file's report names the first failure (dcq.rep_at), which is at the count of the files before it (dcq.ff_front).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_answer_skip_names_first_failure(pre, mid, post, clean, ok):
  %Equal.sym(List<&2, Cm.Note>, DocCommitChoices.notes_of(Cm.answer(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid), Cm.Untried{} <> post))), Cm.reports(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid), Cm.Untried{} <> post), Cm.first.failed(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid), Cm.Untried{} <> post), 0n)), LC.dcq.notes(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid), Cm.Untried{} <> post), ok)) : {List.get(&2, Cm.Note, _, List.length(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid))) == Some{Cm.Skipped{List.length(&2, Cm.Fate, pre)}} : Maybe<&2, Cm.Note>}
  Equal.trans(Maybe<&2, Cm.Note>, List.get(&2, Cm.Note, Cm.reports(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid), Cm.Untried{} <> post), Cm.first.failed(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid), Cm.Untried{} <> post), 0n)), List.length(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid))), Some{Cm.Skipped{Cm.first.failed(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid), Cm.Untried{} <> post), 0n)}}, Some{Cm.Skipped{List.length(&2, Cm.Fate, pre)}}, LC.dcq.rep_at(List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid), Cm.Untried{}, post, Cm.first.failed(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid), Cm.Untried{} <> post), 0n)), Equal.cong(Nat, Maybe<&2, Cm.Note>, z => Some{Cm.Skipped{z}}, Cm.first.failed(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid), Cm.Untried{} <> post), 0n), List.length(&2, Cm.Fate, pre), Equal.trans(Nat, Cm.first.failed(List.append(&2, Cm.Fate, List.append(&2, Cm.Fate, pre, Cm.Wrote{Cm.Fails{}} <> mid), Cm.Untried{} <> post), 0n), Nat.add(List.length(&2, Cm.Fate, pre), 0n), List.length(&2, Cm.Fate, pre), LC.dcq.ff_front(pre, mid, Cm.Untried{} <> post, 0n, clean), LA.dcl.add_zero(List.length(&2, Cm.Fate, pre)))))
