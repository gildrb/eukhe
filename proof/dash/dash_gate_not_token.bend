# eukhe: the proof of LAW dash_gate_not_token
#
# PROOF: what the pairing presents is R1's (dash_token_spec): no token and
# not empty, so junk (gnt.junk), which is refused as a wrong link; a text
# too long for the wire is junk at once.

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./base.bend as LA
import ./dash_token_spec.bend as PDashTokenSpec

def gnt.junk(m: Maybe<&2, List<&2, Nat>>, e: Bool, +f: Da.Disk, +b: Bool, hm: {Dash.sp_has(m) == False{} : Bool}, he: {e == False{} : Bool}) -> {Da.gate.shown(Dash.sp_shown.of(m, e), f, b) == Da.Refuse{Dash.sp_wrong()} : Da.Pass}:
  match m:
    case Some{bs}:
      LA.dashboard_auth.pa.absurdT({Da.gate.shown(Dash.sp_shown.of(Some{bs}, e), f, b) == Da.Refuse{Dash.sp_wrong()} : Da.Pass}, hm)
    case None{}:
      match e:
        case True{}:
          LA.dashboard_auth.pa.absurdT({Da.gate.shown(Dash.sp_shown.of(None{}, True{}), f, b) == Da.Refuse{Dash.sp_wrong()} : Da.Pass}, he)
        case False{}:
          {==}

def gnt.spoken(+t: String, +f: Da.Disk, +b: Bool, junk: {Dash.sp_has(Dash.sp_token(t)) == False{} : Bool}, said: {String.is_empty(t) == False{} : Bool}) -> {Da.gate(Da.Pair{Da.Spoken{t}}, f, b) == Da.Refuse{Dash.sp_wrong()} : Da.Pass}:
  %Equal.sym(Da.Shown, Da.shown(Da.Spoken{t}), Dash.sp_shown(Da.Spoken{t}), Dash.dash_token_spec(Da.Spoken{t})) : {Da.gate.shown(_, f, b) == Da.Refuse{Dash.sp_wrong()} : Da.Pass}
  gnt.junk(Dash.sp_token(t), String.is_empty(t), f, b, junk, said)

def Dash.dash_gate_not_token(t, f, b, junk, said):
  (gnt.spoken(t, f, b, junk, said), {==})
