# eukhe: the proof of LAW rebase_identity_when_head_is_base
#
# PROOF: the rule is the spec's (rr.refines); valid edits have no
# first bad edit (rb.none_true) and the base has its own lines
# (rb.same_refl), so the spec answers the edits.

import Base
import ../../bend/rebase.bend as R
import ../../spec/harness/rebase.bend as RbSpec
import ../../laws/rebase.bend as Rebase
import ./base.bend as LR
import ./base/refines.bend as LRR


def Rebase.rebase_identity_when_head_is_base(b, es, ok):
  +n = List.length(&2, Nat, b)
  %Equal.sym(R.Outcome, R.rebase(b, b, es), RbSpec.rebase(b, b, es), LRR.rr.refines(b, b, es)) : {_ == R.Rebased{es} : R.Outcome}
  %Equal.sym(Maybe<&2, Nat>, RbSpec.bad(es, n), None{}, LR.rb.none_true(RbSpec.bad(es, n), ok)) : {RbSpec.rebase.of(_, RbSpec.same(b, b), b, b, es) == R.Rebased{es} : R.Outcome}
  %Equal.sym(Bool, RbSpec.same(b, b), True{}, LR.rb.same_refl(b)) : {RbSpec.rebase.of(None{}, _, b, b, es) == R.Rebased{es} : R.Outcome}
  {==}
