# eukhe: the proof of LAW gate_write_auto_never_secret

import Base
import ../../laws/path_policy/gate.bend as PathPolicyGate
import ./base.bend as LA

def PathPolicyGate.gate_write_auto_never_secret(c, auto, ans, ran, no):
  LA.pp.gate_write_auto_never_secret(c, auto, ans, ran, no)
