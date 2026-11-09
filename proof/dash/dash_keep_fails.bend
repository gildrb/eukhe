# eukhe: the proof of LAW dash_keep_fails
#
# PROOF: the file's token is R2's (dash_stored_spec), none here, so the
# start choice is tokenless (pa.held_none); the other cases compute.

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./base.bend as LA
import ./dash_stored_spec.bend as PDashStoredSpec

# the file's token, read by the code, is there as R2 says
def dkf.has(+f: Da.Disk, -x: Bool, e: {Dash.sp_has(Dash.sp_stored(f)) == x : Bool}) -> {Dash.sp_has(Da.stored(f)) == x : Bool}:
  Equal.trans(Bool, Dash.sp_has(Da.stored(f)), Dash.sp_has(Dash.sp_stored(f)), x, Equal.cong(Maybe<&2, List<&2, Nat>>, Bool, z => Dash.sp_has(z), Da.stored(f), Dash.sp_stored(f), Dash.dash_stored_spec(f)), e)

def Dash.dash_keep_fails(s, m, none):
  ({==}, (LA.pa.held_none(Da.stored(Da.Holds{s}), m, dkf.has(Da.Holds{s}, False{}, none)), {==}))
