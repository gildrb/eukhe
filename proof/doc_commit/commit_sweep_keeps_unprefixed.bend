# eukhe: the proof of LAW commit_sweep_keeps_unprefixed
#
# PROOF: the code's prefix test is Base's String.starts_with (dcq.starts_sw), so the entry is not swept (dcq.no_sweep) and the indices split around it (dcq.kept_at).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_sweep_keeps_unprefixed(h, pre, n, held, post, other):
  LC.dcq.kept_at(Cm.prefix(h), pre, Cm.Ent{n, held}, post, LC.dcq.no_sweep(Cm.prefix(h), n, held, Equal.trans(Bool, Cm.starts(Cm.prefix(h), n), String.starts_with(n, Cm.prefix(h)), False{}, LC.dcq.starts_sw(Cm.prefix(h), n), other)))
