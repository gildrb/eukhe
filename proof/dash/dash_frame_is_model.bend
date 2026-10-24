# eukhe: the proof of LAW dash_frame_is_model
#
# PROOF: with the file holding a token (dash_stored_spec), a later frame
# passes exactly when Rust found the tokens equal (fm.pass); the model
# runs the frame of c exactly then (fm.ran: a run frame of c is a frame of
# c).

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./base.bend as LA
import ./dash_stored_spec.bend as PDashStoredSpec

# with a token held, the check passes exactly when the tokens are the same
def fm.pass(m: Maybe<&2, List<&2, Nat>>, b: Bool, held: {Maybe.is_some(&2, List<&2, Nat>, m) == True{} : Bool}) -> {Dash.sp_opens(Da.check(m, b)) == b : Bool}:
  match m:
    case None{}:
      LA.dashboard_auth.pa.absurdF({Dash.sp_opens(Da.check(None{}, b)) == b : Bool}, held)
    case Some{bs}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}

def fm.ran(+c: Nat, b: Bool) -> {b == Da.ran(c, Da.frame.ran(c, b)) : Bool}:
  match b:
    case True{}:
      LA.pa.eq_refl(c)
    case False{}:
      {==}

# a frame on a held token passes exactly when the tokens are the same
def fm.frame(+f: Da.Disk, +b: Bool, held: {Maybe.is_some(&2, List<&2, Nat>, Dash.sp_stored(f)) == True{} : Bool}) -> {Dash.sp_opens(Da.frame(f, b)) == b : Bool}:
  %Equal.sym(Maybe<&2, List<&2, Nat>>, Da.stored(f), Dash.sp_stored(f), Dash.dash_stored_spec(f)) : {Dash.sp_opens(Da.check(_, b)) == b : Bool}
  fm.pass(Dash.sp_stored(f), b, held)

def Dash.dash_frame_is_model(cur, t, c, f, held):
  +b = Nat.is_eq(t, cur)
  Equal.trans(Bool, Dash.sp_opens(Da.frame(f, b)), b, Da.ran(c, Da.frame.ran(c, b)), fm.frame(f, b, held), fm.ran(c, b))
