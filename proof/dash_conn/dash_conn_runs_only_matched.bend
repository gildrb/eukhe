# eukhe: the proof of LAW dash_conn_runs_only_matched
#
# PROOF: by cases on the socket and the event. Only a later frame of a
# paired socket can run (a first frame's pass pairs or refuses:
# dcr.first_not_run; the rest compute). Its pass is the check of the
# stored token, which is the spec's (dash_stored_spec), against Rust's
# match: it runs only with a token stored and a match (dro.later_ran).

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash.bend as Dash
import ../../laws/dash_conn.bend as DashConn
import ../dash/dash_stored_spec.bend as PDashStoredSpec
import ./base.bend as LA

def dro.later_ran(mm: Maybe<&2, List<&2, Nat>>, b: Bool, h: {DashConn.cv_is_run(DashConn.cv_verdict(Da.frame.pass(Da.check(mm, b)))) == True{} : Bool}) -> {Bool.and(b, Maybe.is_some(&2, List<&2, Nat>, mm)) == True{} : Bool}:
  match mm:
    case None{}:
      LA.dcn.absurdF({Bool.and(b, False{}) == True{} : Bool}, h)
    case Some{bs}:
      match b:
        case True{}:
          {==}
        case False{}:
          LA.dcn.absurdF({False{} == True{} : Bool}, h)

def dro.runs(c: Da.Conn, e: Da.CEv, ran: {DashConn.cv_is_run(DashConn.cv_verdict(Da.cstep(c, e))) == True{} : Bool}) -> {DashConn.cv_frame_ok(c, e) == True{} : Bool}:
  match c:
    case Da.Waiting{}:
      match e:
        case Da.CFirst{+x, +f, +m}:
          LA.dcn.contra({False{} == True{} : Bool}, DashConn.cv_is_run(DashConn.cv_verdict(Da.first.pass(Da.gate(x, f, m)))), LA.dcr.first_not_run(Da.gate(x, f, m)), ran)
        case Da.CFrame{f, m}:
          LA.dcn.absurdF({False{} == True{} : Bool}, ran)
    case Da.Paired{}:
      match e:
        case Da.CFirst{x, f, m}:
          LA.dcn.absurdF({False{} == True{} : Bool}, ran)
        case Da.CFrame{+f, +m}:
          %Dash.dash_stored_spec(f) : {Bool.and(m, Maybe.is_some(&2, List<&2, Nat>, _)) == True{} : Bool}
          dro.later_ran(Da.stored(f), m, ran)
    case Da.Closed{}:
      LA.dcn.absurdF({False{} == True{} : Bool}, ran)

def DashConn.dash_conn_runs_only_matched(c, e, ran):
  dro.runs(c, e, ran)
