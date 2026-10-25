# eukhe: the proof of LAW dash_conn_entry_history
#
# PROOF: the open is a waiting socket; then by induction on the events,
# each spelled event moves the stepper as the spec's step does and answers
# its spelled verdict (dash_conn_entry_answers), so the next state is the
# spec's socket after it and the rest follows.

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../laws/dash_conn.bend as DashConn
import ./dash_conn_entry_answers.bend as PDashConnEntryAnswers
import ./base.bend as LA

def dceh.step(t: List<&2, Da.CEv>, r: Da.Conn & Da.Verdict, ih: @c2: Da.Conn -> @o2: String -> {DashConn.cs_feed(t, (FDa.Live{c2}, o2)) == o2 <> DashConn.cs_replies(t, c2) : List<&2, String>}) -> {DashConn.cs_feed(t, DashConn.cs_reply(r)) == DashConn.sp_w_verdict(DashConn.cv_verdict(r)) <> DashConn.cs_replies(t, DashConn.cv_conn(r)) : List<&2, String>}:
  (c2, v) = r
  ih(c2, DashConn.sp_w_verdict(v))

def dceh.go(es: List<&2, Da.CEv>, +c: Da.Conn, out: String, fits: {DashConn.sp_fit_evs(es) == True{} : Bool}) -> {DashConn.cs_feed(es, (FDa.Live{c}, out)) == out <> DashConn.cs_replies(es, c) : List<&2, String>}:
  match es:
    case Nil{}:
      {==}
    case +e <> +t:
      +f2 = fits
      %Equal.sym(FDa.St & String, FDa.step(FDa.Live{c}, DashConn.sp_w_ev(e, "")), DashConn.cs_reply(DashConn.sp_cstep(c, e)), DashConn.dash_conn_entry_answers(c, e, LA.dcn.and_l(DashConn.sp_fit_ev(e), DashConn.sp_fit_evs(t), f2))) : {out <> DashConn.cs_feed(t, _) == out <> DashConn.cs_replies(e <> t, c) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, z => out <> z, DashConn.cs_feed(t, DashConn.cs_reply(DashConn.sp_cstep(c, e))), DashConn.cs_replies(e <> t, c), dceh.step(t, DashConn.sp_cstep(c, e), c2 => o2 => dceh.go(t, c2, o2, LA.dcn.and_r(DashConn.sp_fit_ev(e), DashConn.sp_fit_evs(t), f2))))

def DashConn.dash_conn_entry_history(es, fits):
  dceh.go(es, Da.Waiting{}, "", fits)
