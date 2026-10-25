# eukhe: the proof of LAW dash_access_origin_spec
#
# PROOF: the code cuts the origin at its first "://" as the spec does
# (dab.sep), takes the same default port (dab.scheme), reads both
# authorities as the spec does (dab.split) and compares them the same way
# (dab.pair).

import Base
import ../../bend/dash_access.bend as Ac
import ../../laws/dash_access.bend as DashAccess
import ./base.bend as LA

def DashAccess.dash_access_origin_spec(o, h):
  %LA.dab.sep(o) : {Ac.same_origin(o, h) == DashAccess.sp_origin.cut(_, h) : Bool}
  LA.dab.ocut(Ac.sep(o), h)
