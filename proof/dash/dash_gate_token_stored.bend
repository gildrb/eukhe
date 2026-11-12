# eukhe: the proof of LAW dash_gate_token_stored
#
# PROOF: a presented token is checked against the file (gt.hex, by
# dash_token_spec); the file's token is R2's (dash_stored_spec), there
# here, so Rust's report decides (pa.check_some).

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./base.bend as LA
import ./dash_token_spec.bend as PDashTokenSpec
import ./dash_stored_spec.bend as PDashStoredSpec

# a pairing that presents a token is checked as the file and Rust's
# report say (what it presents is R1's: dash_token_spec)
def gt.of(m: Maybe<&2, List<&2, Nat>>, e: Bool, +f: Da.Disk, +b: Bool, hm: {Dash.sp_has(m) == True{} : Bool}) -> {Da.gate.shown(Dash.sp_shown.of(m, e), f, b) == Da.check(Da.stored(f), b) : Da.Pass}:
  match m:
    case None{}:
      LA.dashboard_auth.pa.absurdF({Da.gate.shown(Dash.sp_shown.of(None{}, e), f, b) == Da.check(Da.stored(f), b) : Da.Pass}, hm)
    case Some{bs}:
      {==}

def gt.hex(+t: String, +f: Da.Disk, +b: Bool, token: {Dash.sp_has(Dash.sp_token(t)) == True{} : Bool}) -> {Da.gate(Da.Pair{Da.Spoken{t}}, f, b) == Da.check(Da.stored(f), b) : Da.Pass}:
  %Equal.sym(Da.Shown, Da.shown(Da.Spoken{t}), Dash.sp_shown(Da.Spoken{t}), Dash.dash_token_spec(Da.Spoken{t})) : {Da.gate.shown(_, f, b) == Da.check(Da.stored(f), b) : Da.Pass}
  gt.of(Dash.sp_token(t), String.is_empty(t), f, b, token)

# the file's token, read by the code, is there as R2 says
def gts.has(+f: Da.Disk, -x: Bool, e: {Dash.sp_has(Dash.sp_stored(f)) == x : Bool}) -> {Dash.sp_has(Da.stored(f)) == x : Bool}:
  Equal.trans(Bool, Dash.sp_has(Da.stored(f)), Dash.sp_has(Dash.sp_stored(f)), x, Equal.cong(Maybe<&2, List<&2, Nat>>, Bool, z => Dash.sp_has(z), Da.stored(f), Dash.sp_stored(f), Dash.dash_stored_spec(f)), e)

def Dash.dash_gate_token_stored(t, f, token, holds):
  +h2 = gts.has(f, True{}, holds)
  +tk = token
  (Equal.trans(Da.Pass, Da.gate(Da.Pair{Da.Spoken{t}}, f, True{}), Da.check(Da.stored(f), True{}), Da.Admit{}, gt.hex(t, f, True{}, tk), LA.pa.check_some(Da.stored(f), True{}, h2)), Equal.trans(Da.Pass, Da.gate(Da.Pair{Da.Spoken{t}}, f, False{}), Da.check(Da.stored(f), False{}), Da.Refuse{Dash.sp_wrong()}, gt.hex(t, f, False{}, tk), LA.pa.check_some(Da.stored(f), False{}, h2)))
