# eukhe: the proof of LAW dash_stored_spec
#
# PROOF: the code's trim is the spec's strip of both ends (tm.trim), and
# the code's token is the spec's (hx.token); the other files hold none on
# both sides.

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ./dash_token_spec/hex.bend as LHex
import ./dash_stored_spec/trim.bend as LTrim

def st.holds(+s: String) -> {Da.parse(Da.trim(s)) == Dash.sp_token(Dash.sp_rstrip(Dash.sp_lstrip(s))) : Maybe<&2, List<&2, Nat>>}:
  %Equal.sym(String, Da.trim(s), Dash.sp_rstrip(Dash.sp_lstrip(s)), LTrim.tm.trim(s)) : {Da.parse(_) == Dash.sp_token(Dash.sp_rstrip(Dash.sp_lstrip(s))) : Maybe<&2, List<&2, Nat>>}
  LHex.hx.token(Dash.sp_rstrip(Dash.sp_lstrip(s)))

def st.stored(f: Da.Disk) -> {Da.stored(f) == Dash.sp_stored(f) : Maybe<&2, List<&2, Nat>>}:
  match f:
    case Da.NoFile{}:
      {==}
    case Da.Unread{}:
      {==}
    case Da.Holds{+s}:
      st.holds(s)
    case Da.Huge{}:
      {==}

def Dash.dash_stored_spec(f):
  st.stored(f)
