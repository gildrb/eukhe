# eukhe: the proof of LAW commit_sweep_spares_other_targets
#
# PROOF: past the common `.eukhe-tmp-`, two different dashless digests part before either's `-` (dcq.pf), so the other target's entry is not swept (dcq.no_sweep) and the indices split around it (dcq.kept_at).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_sweep_spares_other_targets(h, g, rest, held, pre, post, hd, gd, ne):
  LC.dcq.kept_at(Cm.prefix(h), pre, Cm.Ent{String.append(DocCommit.tmp_prefix(g), rest), held}, post, LC.dcq.no_sweep(Cm.prefix(h), String.append(DocCommit.tmp_prefix(g), rest), held, LC.dcq.pf(h, g, rest, hd, gd, ne)))
