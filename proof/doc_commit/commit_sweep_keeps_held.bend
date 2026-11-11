# eukhe: the proof of LAW commit_sweep_keeps_held
#
# PROOF: a held entry is not swept (dcq.and_false), so the indices split around it (dcq.kept_at).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_sweep_keeps_held(h, pre, n, post):
  ({==}, LC.dcq.kept_at(Cm.prefix(h), pre, Cm.Ent{n, True{}}, post, LC.dcq.and_false(Cm.starts(Cm.prefix(h), n))))
