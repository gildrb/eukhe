# eukhe: the proof of LAW verify_record_writes_one
#
# PROOF: LA.va.record_all: the revision equals itself and put at an index
# below the length writes that one slot (induction on the index and the
# slots), read back at every index j (induction on j with them).

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/act.bend as LA

def Verify.verify_record_writes_one(i, v, at, rev, slots, claimed, tries, j, has):
  LA.va.record_all(i, v, at, rev, slots, claimed, tries, j, has)
