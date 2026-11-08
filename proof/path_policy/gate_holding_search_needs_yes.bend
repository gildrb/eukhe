# eukhe: the proof of LAW gate_holding_search_needs_yes
#
# PROOF: a search of a directory that holds a secret has the effects read
# and secret whatever its class; the auto test never grants the secret
# effect, so the gate's verdict computes to the answer's yes test.

import Base
import ../../laws/path_policy/gate.bend as PathPolicyGate
import ./gate_secret_needs_yes.bend as PGateSecretNeedsYes

def PathPolicyGate.gate_holding_search_needs_yes(c, auto, ans, ran):
  PGateSecretNeedsYes.pgs.yes(ans, ran)
