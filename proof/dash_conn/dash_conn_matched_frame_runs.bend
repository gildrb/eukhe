# eukhe: the proof of LAW dash_conn_matched_frame_runs
#
# PROOF: the frame's pass checks the stored token, which is the spec's
# (dash_stored_spec); the file holds one, and Rust matched: it runs and
# the socket stays paired (dmf.holds).

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ../dash/dash_stored_spec.bend as PDashStoredSpec
import ./base.bend as LA

def dmf.holds(mm: Maybe<&2, List<&2, Nat>>, h: {Maybe.is_some(&2, List<&2, Nat>, mm) == True{} : Bool}) -> {Da.frame.pass(Da.check(mm, True{})) == (Da.Paired{}, Da.VRun{}) : Da.Conn & Da.Verdict}:
  match mm:
    case None{}:
      LA.dcn.absurdF({Da.frame.pass(Da.check(None{}, True{})) == (Da.Paired{}, Da.VRun{}) : Da.Conn & Da.Verdict}, h)
    case Some{bs}:
      {==}

def DashConn.dash_conn_matched_frame_runs(f, holds):
  %Equal.sym(Maybe<&2, List<&2, Nat>>, Da.stored(f), Dash.sp_stored(f), Dash.dash_stored_spec(f)) : {Da.frame.pass(Da.check(_, True{})) == (Da.Paired{}, Da.VRun{}) : Da.Conn & Da.Verdict}
  dmf.holds(Dash.sp_stored(f), holds)
