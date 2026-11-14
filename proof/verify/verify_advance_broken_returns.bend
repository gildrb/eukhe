# eukhe: the proof of LAW verify_advance_broken_returns
#
# PROOF: the step is a return with the broken checks opened
# (LA.va.broken_is: none is due, the label is the spec's by LAW
# verify_label_is_spec, unverified by the premise, a check and room); the
# slot at every index of the code's reopen is the spec's rerun
# (LA.va.reopen_nth).

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/act.bend as LA
import ./verify_label_is_spec.bend as PLabel

def Verify.verify_advance_broken_returns(conf, now, cap, rev, s, t, tries, j, done, un, room):
  %LA.va.broken_is(conf, now, cap, rev, s, t, tries, done, un, room, Verify.verify_label_is_spec(conf, now, s <> t)) : LA.va.Returned(j, now, rev, s <> t, tries, _)
  ({==}, ({==}, (LA.va.reopen_nth(now, s <> t, j), ({==}, {==}))))
