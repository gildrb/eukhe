# eukhe: the proof of LAW dash_access_host_spec
#
# PROOF: the code reads the authority as the spec does (dab.split: each
# scan and choice, helper by helper) and tests its host against the same
# names (dab.host_of).

import Base
import ../../bend/dash_access.bend as Ac
import ../../laws/dash_access.bend as DashAccess
import ./base.bend as LA

def DashAccess.dash_access_host_spec(h, al):
  %LA.dab.split(h) : {Ac.host_allowed(h, al) == DashAccess.sp_host.of(_, al) : Bool}
  LA.dab.host_of(Ac.split(h), al)
