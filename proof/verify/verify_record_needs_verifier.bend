# eukhe: the proof of LAW verify_record_needs_verifier
#
# PROOF: every actor: the owner's and the worker's Record compute to the
# refusal; the verifier refutes the premise.

import Base
import ../../bend/verify.bend as V
import ../../spec/verified/verify.bend as S
import ../../laws/verify.bend as Verify
import ./base/act.bend as LA

def Verify.verify_record_needs_verifier(who, of, i, v, at, a, other):
  match who:
    case V.Owner{}:
      {==}
    case V.Worker{}:
      {==}
    case V.Verifier{}:
      LA.va.absurd_tf({V.act(V.Verifier{}, V.Record{of, i, v, at}, a) == (False{}, a) : Bool & V.Acc}, other)
