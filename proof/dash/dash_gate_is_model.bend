# eukhe: the proof of LAW dash_gate_is_model
#
# PROOF: a presented text that is a token (hx.token) shows as Hex; with
# the file holding a token the socket then opens exactly when Rust found
# the tokens equal (dash_frame_is_model's fm.frame), which is the model's
# admit of t against cur; a frame that is no pairing is refused, and the
# model admits no missing token.

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./base.bend as LA
import ./dash_token_spec/hex.bend as LHex
import ./dash_frame_is_model.bend as PDashFrameIsModel

def gm.tok(m: Maybe<&2, List<&2, Nat>>, e: Bool, +f: Da.Disk, +b: Bool, tok: {Maybe.is_some(&2, List<&2, Nat>, m) == True{} : Bool}, held: {Maybe.is_some(&2, List<&2, Nat>, Dash.sp_stored(f)) == True{} : Bool}) -> {Dash.sp_opens(Da.gate.shown(Da.shown.of(m, e), f, b)) == b : Bool}:
  match m:
    case None{}:
      LA.dashboard_auth.pa.absurdF({Dash.sp_opens(Da.gate.shown(Da.shown.of(None{}, e), f, b)) == b : Bool}, tok)
    case Some{bs}:
      PDashFrameIsModel.fm.frame(f, b, held)

def Dash.dash_gate_is_model(cur, t, p, f, shown, tok, held):
  +b = Nat.is_eq(t, cur)
  %Equal.sym(Maybe<&2, List<&2, Nat>>, Da.parse(p), Dash.sp_token(p), LHex.hx.token(p)) : {Dash.sp_opens(Da.gate.shown(Da.shown.of(_, String.is_empty(p)), f, b)) == b : Bool} & {Dash.sp_opens(Da.gate(Da.NotPairing{}, f, False{})) == Da.admit(cur, None{}) : Bool}
  (gm.tok(Dash.sp_token(p), String.is_empty(p), f, b, tok, held), {==})
