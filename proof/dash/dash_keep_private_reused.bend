# eukhe: the proof of LAW dash_keep_private_reused
#
# PROOF: the file's token is R2's (dash_stored_spec), there here, so the
# mode decides (pa.held_some). A mode of 64 u leaves 0 by 64: each 64
# counts one more quotient and starts the remainder again (km.zero, by
# induction on u), so the file is reused.

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./base.bend as LA
import ./dash_stored_spec.bend as PDashStoredSpec

# the file's token, read by the code, is there as R2 says
def kpr.has(+f: Da.Disk, -x: Bool, e: {Dash.sp_has(Dash.sp_stored(f)) == x : Bool}) -> {Dash.sp_has(Da.stored(f)) == x : Bool}:
  Equal.trans(Bool, Dash.sp_has(Da.stored(f)), Dash.sp_has(Dash.sp_stored(f)), x, Equal.cong(Maybe<&2, List<&2, Nat>>, Bool, z => Dash.sp_has(z), Da.stored(f), Dash.sp_stored(f), Dash.dash_stored_spec(f)), e)

# 64 u leaves 0 by 64
def km.zero(u: Nat, +d: Nat) -> {Pair.snd(Nat, Nat, Nat.divmod.go(Nat.mul(u, 64n), 63n, d, 0n)) == 0n : Nat}:
  match u:
    case 0n:
      {==}
    case 1n+p:
      km.zero(p, 1n+d)

def Dash.dash_keep_private_reused(s, u, holds):
  +h2 = kpr.has(Da.Holds{s}, True{}, holds)
  %Equal.sym(Da.Keep, Da.keep.held(Da.stored(Da.Holds{s}), Nat.mul(u, 64n)), Da.keep.mode(Nat.mul(u, 64n)), LA.pa.held_some(Da.stored(Da.Holds{s}), Nat.mul(u, 64n), h2)) : {_ == Da.Reuse{} : Da.Keep}
  %Equal.sym(Nat, Pair.snd(Nat, Nat, Nat.divmod.go(Nat.mul(u, 64n), 63n, 0n, 0n)), 0n, km.zero(u, 0n)) : {Da.keep.private(Nat.is_eq(_, 0n)) == Da.Reuse{} : Da.Keep}
  {==}
