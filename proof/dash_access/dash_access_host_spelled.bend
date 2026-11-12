# eukhe: the proof of LAW dash_access_host_spelled
#
# PROOF: a well-formed writing reads as its host and port (LA.dab.
# split_spell: no forbidden char, then the IPv6 literal closes at the ']'
# after its inside, or the text splits at the ':' before the port, which
# holds no ':'; the digits read as their value, never capped below
# 65536); the code's host test is then R2's (LA.dab.named: the code's
# comparison is the spec's ASCII-case equality).

import Base
import ../../bend/dash_access.bend as Ac
import ../../laws/dash_access.bend as DashAccess
import ./base.bend as LA

def DashAccess.dash_access_host_spelled(a, al, ok):
  %Equal.sym(Ac.Authority, Ac.split(DashAccess.sp_spell(a)), Ac.HostPort{DashAccess.sp_name(a), DashAccess.sp_port(a)}, LA.dab.split_spell(a, ok)) : {Ac.host_allowed.of(_, al) == DashAccess.sp_named(DashAccess.sp_name(a), al) : Bool}
  LA.dab.named(DashAccess.sp_name(a), DashAccess.sp_port(a), al)
