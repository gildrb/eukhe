# eukhe: the proof of LAW commit_check_stops_at_changed
#
# PROOF: n clear files move the check's index on by n (dcq.skip); the next file stops it there.

import Base
import ../../bend/doc_commit.bend as Cm
import ../../laws/base.bend as LawsBase
import ../../laws/doc_commit.bend as DocCommit
import ../../laws/doc_commit/choices.bend as DocCommitChoices
import ./base.bend as LA
import ./base/choices.bend as LC

def DocCommitChoices.commit_check_stops_at_changed(n, t, post):
  Equal.trans(Cm.Check, Cm.check.go(List.append(&2, Cm.Met, DocCommitChoices.clears(n), Cm.Met{True{}, t} <> post), 0n), Cm.check.go(Cm.Met{True{}, t} <> post, Nat.add(n, 0n)), Cm.Stop{n, Cm.Changed{}}, LC.dcq.skip(n, Cm.Met{True{}, t} <> post, 0n), Equal.cong(Nat, Cm.Check, z => Cm.Stop{z, Cm.Changed{}}, Nat.add(n, 0n), n, LA.dcl.add_zero(n)))
