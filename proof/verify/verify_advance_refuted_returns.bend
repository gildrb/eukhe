# eukhe: the proof of LAW verify_advance_refuted_returns
#
# PROOF: once the lead is the number of checks none is due (LA.va.due_none);
# the label is the spec's (LAW verify_label_is_spec), failed by the
# premise; with room the settling returns.

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/act.bend as LA
import ./verify_label_is_spec.bend as PLabel

def Verify.verify_advance_refuted_returns(now, cap, rev, slots, tries, done, bad, room):
  %room : {V.advance(now, cap, V.Acc{rev, slots, True{}, tries}) == V.settle.failed(_, rev, slots, tries) : V.Action & V.Acc}
  %bad : {V.advance(now, cap, V.Acc{rev, slots, True{}, tries}) == V.settle(_, now, cap, rev, slots, tries) : V.Action & V.Acc}
  %Verify.verify_label_is_spec(now, slots) : {V.advance(now, cap, V.Acc{rev, slots, True{}, tries}) == V.settle(_, now, cap, rev, slots, tries) : V.Action & V.Acc}
  %LA.va.due_none(now, slots, done) : {V.advance(now, cap, V.Acc{rev, slots, True{}, tries}) == V.advance.go(_, now, cap, rev, slots, tries) : V.Action & V.Acc}
  {==}
