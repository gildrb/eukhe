# eukhe: the proof of LAW dash_conn_unmatched_ends
#
# PROOF: by cases on the socket. A closed socket answers only `closed`
# (dcr.closed_run). A waiting or paired socket refuses an event Rust did
# not match (dum.refused_w, dum.refused_p: whatever the frame and the
# file, a pass without a match refuses), so that verdict neither runs nor
# opens (dum.quiet) and nothing after it does
# (dash_conn_refused_runs_nothing).

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash_conn.bend as DashConn
import ./dash_conn_refused_runs_nothing.bend as PDashConnRefusedRunsNothing
import ./base.bend as LA

def dum.check_first(mm: Maybe<&2, List<&2, Nat>>) -> {DashConn.cv_is_refuse(DashConn.cv_verdict(Da.first.pass(Da.check(mm, False{})))) == True{} : Bool}:
  match mm:
    case None{}:
      {==}
    case Some{bs}:
      {==}

def dum.check_later(mm: Maybe<&2, List<&2, Nat>>) -> {DashConn.cv_is_refuse(DashConn.cv_verdict(Da.frame.pass(Da.check(mm, False{})))) == True{} : Bool}:
  match mm:
    case None{}:
      {==}
    case Some{bs}:
      {==}

def dum.shown(s: Da.Shown, f: Da.Disk) -> {DashConn.cv_is_refuse(DashConn.cv_verdict(Da.first.pass(Da.gate.shown(s, f, False{})))) == True{} : Bool}:
  match s:
    case Da.Hex{bs}:
      dum.check_first(Da.stored(f))
    case Da.Blank{}:
      {==}
    case Da.Junk{}:
      {==}

# a first frame without Rust's match is refused
def dum.gate(x: Da.First, f: Da.Disk) -> {DashConn.cv_is_refuse(DashConn.cv_verdict(Da.first.pass(Da.gate(x, f, False{})))) == True{} : Bool}:
  match x:
    case Da.NoText{}:
      {==}
    case Da.NotPairing{}:
      {==}
    case Da.Pair{t}:
      dum.shown(Da.shown(t), f)

def dum.refused_w(e: Da.CEv, h: {DashConn.cv_matches(e) == False{} : Bool}) -> {DashConn.cv_is_refuse(DashConn.cv_verdict(Da.cstep(Da.Waiting{}, e))) == True{} : Bool}:
  match e:
    case Da.CFirst{x, f, m}:
      match m:
        case True{}:
          LA.dcn.absurdT({DashConn.cv_is_refuse(DashConn.cv_verdict(Da.cstep(Da.Waiting{}, Da.CFirst{x, f, True{}}))) == True{} : Bool}, h)
        case False{}:
          dum.gate(x, f)
    case Da.CFrame{f, m}:
      {==}

def dum.refused_p(e: Da.CEv, h: {DashConn.cv_matches(e) == False{} : Bool}) -> {DashConn.cv_is_refuse(DashConn.cv_verdict(Da.cstep(Da.Paired{}, e))) == True{} : Bool}:
  match e:
    case Da.CFirst{x, f, m}:
      {==}
    case Da.CFrame{f, m}:
      match m:
        case True{}:
          LA.dcn.absurdT({DashConn.cv_is_refuse(DashConn.cv_verdict(Da.cstep(Da.Paired{}, Da.CFrame{f, True{}}))) == True{} : Bool}, h)
        case False{}:
          dum.check_later(Da.stored(f))

# a refusal neither runs nor opens
def dum.quiet(v: Da.Verdict, h: {DashConn.cv_is_refuse(v) == True{} : Bool}) -> {Bool.or(DashConn.cv_is_run(v), DashConn.cv_is_paired(v)) == False{} : Bool}:
  match v:
    case Da.VPaired{}:
      LA.dcn.absurdF({True{} == False{} : Bool}, h)
    case Da.VRun{}:
      LA.dcn.absurdF({True{} == False{} : Bool}, h)
    case Da.VRefuse{t}:
      {==}
    case Da.VClosed{}:
      {==}

def dum.live(+c: Da.Conn, +e: Da.CEv, +es: List<&2, Da.CEv>, +r: {DashConn.cv_is_refuse(DashConn.cv_verdict(Da.cstep(c, e))) == True{} : Bool}) -> {DashConn.cv_any_live(DashConn.cv_run(e <> es, c)) == False{} : Bool}:
  %Equal.sym(Bool, Bool.or(DashConn.cv_is_run(DashConn.cv_verdict(Da.cstep(c, e))), DashConn.cv_is_paired(DashConn.cv_verdict(Da.cstep(c, e)))), False{}, dum.quiet(DashConn.cv_verdict(Da.cstep(c, e)), r)) : {Bool.or(_, DashConn.cv_any_live(DashConn.cv_run(es, DashConn.cv_conn(Da.cstep(c, e))))) == False{} : Bool}
  DashConn.dash_conn_refused_runs_nothing(c, e, es, r)

def dum.go(c: Da.Conn, +e: Da.CEv, +es: List<&2, Da.CEv>, h: {DashConn.cv_matches(e) == False{} : Bool}) -> {DashConn.cv_any_live(DashConn.cv_run(e <> es, c)) == False{} : Bool}:
  match c:
    case Da.Waiting{}:
      dum.live(Da.Waiting{}, e, es, dum.refused_w(e, h))
    case Da.Paired{}:
      dum.live(Da.Paired{}, e, es, dum.refused_p(e, h))
    case Da.Closed{}:
      LA.dcr.closed_run(es)

def DashConn.dash_conn_unmatched_ends(c, e, es, unmatched):
  dum.go(c, e, es, unmatched)
