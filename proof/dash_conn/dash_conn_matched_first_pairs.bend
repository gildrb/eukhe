# eukhe: the proof of LAW dash_conn_matched_first_pairs
#
# PROOF: the frame is a pairing (dmp.go); what it presents is the spec's
# (dash_token_spec), a token (dmp.shown); the stored token is the spec's
# (dash_stored_spec), held; Rust matched: the socket pairs (dmp.holds).

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ../dash/dash_token_spec.bend as PDashTokenSpec
import ../dash/dash_stored_spec.bend as PDashStoredSpec
import ./base.bend as LA

def dmp.holds(mm: Maybe<&2, List<&2, Nat>>, h: {Maybe.is_some(&2, List<&2, Nat>, mm) == True{} : Bool}) -> {Da.first.pass(Da.check(mm, True{})) == (Da.Paired{}, Da.VPaired{}) : Da.Conn & Da.Verdict}:
  match mm:
    case None{}:
      LA.dcn.absurdF({Da.first.pass(Da.check(None{}, True{})) == (Da.Paired{}, Da.VPaired{}) : Da.Conn & Da.Verdict}, h)
    case Some{bs}:
      {==}

def dmp.shown(s: Da.Shown, +f: Da.Disk, shown: {DashConn.cv_presents.shown(s) == True{} : Bool}, holds: {Maybe.is_some(&2, List<&2, Nat>, Dash.sp_stored(f)) == True{} : Bool}) -> {Da.first.pass(Da.gate.shown(s, f, True{})) == (Da.Paired{}, Da.VPaired{}) : Da.Conn & Da.Verdict}:
  match s:
    case Da.Hex{bs}:
      %Equal.sym(Maybe<&2, List<&2, Nat>>, Da.stored(f), Dash.sp_stored(f), Dash.dash_stored_spec(f)) : {Da.first.pass(Da.check(_, True{})) == (Da.Paired{}, Da.VPaired{}) : Da.Conn & Da.Verdict}
      dmp.holds(Dash.sp_stored(f), holds)
    case Da.Blank{}:
      LA.dcn.absurdF({Da.first.pass(Da.gate.shown(Da.Blank{}, f, True{})) == (Da.Paired{}, Da.VPaired{}) : Da.Conn & Da.Verdict}, shown)
    case Da.Junk{}:
      LA.dcn.absurdF({Da.first.pass(Da.gate.shown(Da.Junk{}, f, True{})) == (Da.Paired{}, Da.VPaired{}) : Da.Conn & Da.Verdict}, shown)

def dmp.go(x: Da.First, +f: Da.Disk, shown: {DashConn.cv_presents(x) == True{} : Bool}, holds: {DashConn.cv_holds(f) == True{} : Bool}) -> {Da.cstep(Da.Waiting{}, Da.CFirst{x, f, True{}}) == (Da.Paired{}, Da.VPaired{}) : Da.Conn & Da.Verdict}:
  match x:
    case Da.NoText{}:
      LA.dcn.absurdF({Da.cstep(Da.Waiting{}, Da.CFirst{Da.NoText{}, f, True{}}) == (Da.Paired{}, Da.VPaired{}) : Da.Conn & Da.Verdict}, shown)
    case Da.NotPairing{}:
      LA.dcn.absurdF({Da.cstep(Da.Waiting{}, Da.CFirst{Da.NotPairing{}, f, True{}}) == (Da.Paired{}, Da.VPaired{}) : Da.Conn & Da.Verdict}, shown)
    case Da.Pair{+t}:
      %Equal.sym(Da.Shown, Da.shown(t), Dash.sp_shown(t), Dash.dash_token_spec(t)) : {Da.first.pass(Da.gate.shown(_, f, True{})) == (Da.Paired{}, Da.VPaired{}) : Da.Conn & Da.Verdict}
      dmp.shown(Dash.sp_shown(t), f, shown, holds)

def DashConn.dash_conn_matched_first_pairs(x, f, shown, holds):
  dmp.go(x, f, shown, holds)
