# eukhe: the proof of LAW verify_advance_broken_ends_at_cap
#
# PROOF: once the lead is the number of checks none is due (LA.va.due_none);
# the label is the spec's (LAW verify_label_is_spec), unverified by the
# premise; with a check and no room the settling ends unverified.

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/act.bend as LA
import ./verify_label_is_spec.bend as PLabel

def Verify.verify_advance_broken_ends_at_cap(conf, now, cap, rev, s, t, tries, done, un, full):
  %full : {V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries}) == V.settle.broken(_, now, rev, s <> t, tries) : V.Action & V.Acc}
  %un : {V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries}) == V.settle(_, now, cap, rev, s <> t, tries) : V.Action & V.Acc}
  %Verify.verify_label_is_spec(conf, now, s <> t) : {V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries}) == V.settle(_, now, cap, rev, s <> t, tries) : V.Action & V.Acc}
  %LA.va.due_none(now, s <> t, done) : {V.advance(conf, now, cap, V.Acc{rev, s <> t, True{}, tries}) == V.advance.go(conf, _, now, cap, rev, s <> t, tries) : V.Action & V.Acc}
  {==}
