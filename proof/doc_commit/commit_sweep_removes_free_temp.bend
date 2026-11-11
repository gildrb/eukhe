# eukhe: the proof of LAW commit_sweep_removes_free_temp
#
# PROOF: the prefix starts a name that begins with it (dcq.starts_app), so the free entry is swept (dcf.freet) at its index (dcq.gone_at).

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def dcf.freet(+h: String, +rest: String) -> {Cm.sweeps(Cm.prefix(h), Cm.Ent{String.append(DocCommit.tmp_prefix(h), rest), False{}}) == True{} : Bool}:
  %Equal.sym(Bool, Cm.starts(Cm.prefix(h), String.append(Cm.prefix(h), rest)), True{}, LC.dcq.starts_app(Cm.prefix(h), rest)) : {Bool.and(_, Bool.not(False{})) == True{} : Bool}
  {==}

def DocCommitChoices.commit_sweep_removes_free_temp(h, pre, rest, post):
  LC.dcq.gone_at(Cm.prefix(h), pre, Cm.Ent{String.append(DocCommit.tmp_prefix(h), rest), False{}}, post, dcf.freet(h, rest))
