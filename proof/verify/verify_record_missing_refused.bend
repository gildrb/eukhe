# eukhe: the proof of LAW verify_record_missing_refused
#
# PROOF: the revision equals itself (LA.va.eq_refl); put finds no slot where
# nth finds none (LA.va.put_none); the refusal computes.

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/act.bend as LA

def Verify.verify_record_missing_refused(i, v, at, rev, slots, claimed, tries, none):
  %LA.va.put_none(i, V.Judged{v, at}, slots, none) : {V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries}) == V.act.put(_, rev, slots, claimed, tries) : Bool & V.Acc}
  %LA.va.eq_refl(rev) : {V.act(V.Verifier{}, V.Record{rev, i, v, at}, V.Acc{rev, slots, claimed, tries}) == V.act.stamp(_, i, V.Judged{v, at}, rev, slots, claimed, tries) : Bool & V.Acc}
  {==}
