# eukhe: the proof of LAW verify_advance_runs_first_due
#
# PROOF: while the lead is below the number of checks the first due check
# is the one at the lead (LA.va.due_some, by induction on the slots over
# every start index); the step computes.

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/act.bend as LA

def Verify.verify_advance_runs_first_due(conf, now, cap, rev, slots, tries, left):
  %LA.va.due_some(now, slots, left) : {V.advance(conf, now, cap, V.Acc{rev, slots, True{}, tries}) == V.advance.go(conf, _, now, cap, rev, slots, tries) : V.Action & V.Acc}
  {==}
