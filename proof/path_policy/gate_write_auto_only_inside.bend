# eukhe: the proof of LAW gate_write_auto_only_inside

import Base
import ../../laws/path_policy.bend as PathPolicy
import ./base.bend as LA

def PathPolicy.gate_write_auto_only_inside(c, auto, ans, ran, no):
  LA.pp.gate_write_auto_only_inside(c, auto, ans, ran, no)
