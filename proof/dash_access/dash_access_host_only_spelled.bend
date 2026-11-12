# eukhe: the proof of LAW dash_access_host_only_spelled
#
# PROOF: an allowed `Host` reads as an authority; every text the code
# reads as one is the writing of a well-formed authority (LA.dab.
# split_inv, stage by stage: the forbidden chars, the ']' close, the last
# ':' cut, the port's sign and digits).

import Base
import ../../bend/dash_access.bend as Ac
import ../../laws/dash_access.bend as DashAccess
import ./base.bend as LA

def dhos.go(-h: String, a: Ac.Authority, sp: LA.dab.SP(h, a), +al: List<&2, String>, yes: {Ac.host_allowed.of(a, al) == True{} : Bool}) -> Sigma<&1, &1, DashAccess.SpAuth, w => {h == DashAccess.sp_spell(w) : String} & {DashAccess.sp_well(w) == True{} : Bool}>:
  match a:
    case Ac.HostPort{n, p}:
      sp
    case Ac.NoAuthority{}:
      LA.dab.absurdF(Sigma<&1, &1, DashAccess.SpAuth, w => {h == DashAccess.sp_spell(w) : String} & {DashAccess.sp_well(w) == True{} : Bool}>, yes)

def DashAccess.dash_access_host_only_spelled(h, al, yes):
  dhos.go(h, Ac.split(h), LA.dab.split_inv(h), al, yes)
