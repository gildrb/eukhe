# eukhe: the proof of LAW verify_advance_refuted_ends_at_cap
#
# PROOF: once the lead is the number of checks none is due (LA.va.due_none);
# the label is the spec's (LAW verify_label_is_spec), failed by the
# premise; with no room the settling ends failed.

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/act.bend as LA
import ./verify_label_is_spec.bend as PLabel

def Verify.verify_advance_refuted_ends_at_cap(conf, now, cap, rev, slots, tries, done, bad, full):
  %full : {V.advance(conf, now, cap, V.Acc{rev, slots, True{}, tries}) == V.settle.failed(_, rev, slots, tries) : V.Action & V.Acc}
  %bad : {V.advance(conf, now, cap, V.Acc{rev, slots, True{}, tries}) == V.settle(_, now, cap, rev, slots, tries) : V.Action & V.Acc}
  %Verify.verify_label_is_spec(conf, now, slots) : {V.advance(conf, now, cap, V.Acc{rev, slots, True{}, tries}) == V.settle(_, now, cap, rev, slots, tries) : V.Action & V.Acc}
  %LA.va.due_none(now, slots, done) : {V.advance(conf, now, cap, V.Acc{rev, slots, True{}, tries}) == V.advance.go(conf, _, now, cap, rev, slots, tries) : V.Action & V.Acc}
  {==}
