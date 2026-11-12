# eukhe: the proof of LAW verify_worker_changes_no_verdict
#
# PROOF: every act: the worker's Assign and Record are refused with the
# acceptance itself; a Claim keeps the slots and the revision.

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify

def Verify.verify_worker_changes_no_verdict(op, a):
  match op:
    case V.Assign{n}:
      ({==}, {==})
    case V.Claim{}:
      match a:
        case V.Acc{rev, slots, claimed, tries}:
          ({==}, {==})
    case V.Record{of, i, v, at}:
      ({==}, {==})
