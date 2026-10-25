# eukhe: the proof of LAW dash_conn_history
#
# PROOF: where the verdicts stand follows where the socket stands (dch.ph:
# waiting, paired, closed). By cases, every step's verdict may come where
# the socket stands (dch.good) and moves the verdicts where the step moves
# the socket (dch.next); by induction on the events the whole run is good
# from every socket state (dch.go), so from a waiting one.

import Base
import ../../bend/dash.bend as Da
import ../../laws/dash_conn.bend as DashConn

# where the verdicts of a socket in c stand
def dch.ph(c: Da.Conn) -> DashConn.Ph:
  match c:
    case Da.Waiting{}:
      DashConn.PhWait{}
    case Da.Paired{}:
      DashConn.PhPaired{}
    case Da.Closed{}:
      DashConn.PhClosed{}

def dch.good_first(p: Da.Pass) -> {DashConn.cv_good(DashConn.PhWait{}, DashConn.cv_verdict(Da.first.pass(p))) == True{} : Bool}:
  match p:
    case Da.Admit{}:
      {==}
    case Da.Refuse{t}:
      {==}

def dch.good_later(p: Da.Pass) -> {DashConn.cv_good(DashConn.PhPaired{}, DashConn.cv_verdict(Da.frame.pass(p))) == True{} : Bool}:
  match p:
    case Da.Admit{}:
      {==}
    case Da.Refuse{t}:
      {==}

def dch.next_first(p: Da.Pass) -> {DashConn.cv_next(DashConn.PhWait{}, DashConn.cv_verdict(Da.first.pass(p))) == dch.ph(DashConn.cv_conn(Da.first.pass(p))) : DashConn.Ph}:
  match p:
    case Da.Admit{}:
      {==}
    case Da.Refuse{t}:
      {==}

def dch.next_later(p: Da.Pass) -> {DashConn.cv_next(DashConn.PhPaired{}, DashConn.cv_verdict(Da.frame.pass(p))) == dch.ph(DashConn.cv_conn(Da.frame.pass(p))) : DashConn.Ph}:
  match p:
    case Da.Admit{}:
      {==}
    case Da.Refuse{t}:
      {==}

# a step's verdict may come where the socket stands
def dch.good(c: Da.Conn, e: Da.CEv) -> {DashConn.cv_good(dch.ph(c), DashConn.cv_verdict(Da.cstep(c, e))) == True{} : Bool}:
  match c:
    case Da.Waiting{}:
      match e:
        case Da.CFirst{x, f, m}:
          dch.good_first(Da.gate(x, f, m))
        case Da.CFrame{f, m}:
          {==}
    case Da.Paired{}:
      match e:
        case Da.CFirst{x, f, m}:
          {==}
        case Da.CFrame{f, m}:
          dch.good_later(Da.frame(f, m))
    case Da.Closed{}:
      {==}

# a step moves the verdicts where it moves the socket
def dch.next(c: Da.Conn, e: Da.CEv) -> {DashConn.cv_next(dch.ph(c), DashConn.cv_verdict(Da.cstep(c, e))) == dch.ph(DashConn.cv_conn(Da.cstep(c, e))) : DashConn.Ph}:
  match c:
    case Da.Waiting{}:
      match e:
        case Da.CFirst{x, f, m}:
          dch.next_first(Da.gate(x, f, m))
        case Da.CFrame{f, m}:
          {==}
    case Da.Paired{}:
      match e:
        case Da.CFirst{x, f, m}:
          {==}
        case Da.CFrame{f, m}:
          dch.next_later(Da.frame(f, m))
    case Da.Closed{}:
      {==}

def dch.go(es: List<&2, Da.CEv>, +c: Da.Conn) -> {DashConn.cv_ok(DashConn.cv_run(es, c), dch.ph(c)) == True{} : Bool}:
  match es:
    case Nil{}:
      {==}
    case +e <> +t:
      %Equal.sym(Bool, DashConn.cv_good(dch.ph(c), DashConn.cv_verdict(Da.cstep(c, e))), True{}, dch.good(c, e)) : {Bool.and(_, DashConn.cv_ok(DashConn.cv_run(t, DashConn.cv_conn(Da.cstep(c, e))), DashConn.cv_next(dch.ph(c), DashConn.cv_verdict(Da.cstep(c, e))))) == True{} : Bool}
      %Equal.sym(DashConn.Ph, DashConn.cv_next(dch.ph(c), DashConn.cv_verdict(Da.cstep(c, e))), dch.ph(DashConn.cv_conn(Da.cstep(c, e))), dch.next(c, e)) : {Bool.and(True{}, DashConn.cv_ok(DashConn.cv_run(t, DashConn.cv_conn(Da.cstep(c, e))), _)) == True{} : Bool}
      dch.go(t, DashConn.cv_conn(Da.cstep(c, e)))

def DashConn.dash_conn_history(es):
  dch.go(es, Da.Waiting{})
