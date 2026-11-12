# eukhe: the proof of LAW verify_assign_needs_owner
#
# PROOF: every actor: the worker's and the verifier's Assign compute to the
# refusal; the owner refutes the premise.

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/act.bend as LA

def Verify.verify_assign_needs_owner(who, n, a, other):
  match who:
    case V.Owner{}:
      LA.va.absurd_tf({V.act(V.Owner{}, V.Assign{n}, a) == (False{}, a) : Bool & V.Acc}, other)
    case V.Worker{}:
      {==}
    case V.Verifier{}:
      {==}
