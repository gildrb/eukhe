# eukhe: the proof of LAW dash_closed_runs_nothing
#
# PROOF: by induction on the inputs: whatever the decoder reads, a closed
# socket stays closed (dcrn.st) and answers `closed` or the malformed
# error (dcrn.q), case by case on the decoder's answer.

import Base
import ../../bend/dash.bend as Da
import ../../bend/ffi_dash.bend as FDa
import ../../bend/wire.bend as Wr
import ../../laws/dash_conn.bend as DashConn
import ./base.bend as LA

def dcrn.st_end(b: Bool, e: Da.CEv) -> {DashConn.cs_st(FDa.step.end(b, Da.Closed{}, e)) == FDa.Live{Da.Closed{}} : FDa.St}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a closed socket stays closed, whatever the input
def dcrn.st(r: Wr.Dec<Da.CEv>) -> {DashConn.cs_st(FDa.step.ev(Da.Closed{}, r)) == FDa.Live{Da.Closed{}} : FDa.St}:
  match r:
    case Wr.Got{e, rest}:
      dcrn.st_end(Wr.end(rest), e)
    case Wr.Bad{}:
      {==}

def dcrn.q_end(b: Bool, e: Da.CEv) -> {DashConn.cw_quiet1(DashConn.cs_out(FDa.step.end(b, Da.Closed{}, e))) == True{} : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# a closed socket answers `closed` or the malformed error
def dcrn.q(r: Wr.Dec<Da.CEv>) -> {DashConn.cw_quiet1(DashConn.cs_out(FDa.step.ev(Da.Closed{}, r))) == True{} : Bool}:
  match r:
    case Wr.Got{e, rest}:
      dcrn.q_end(Wr.end(rest), e)
    case Wr.Bad{}:
      {==}

def DashConn.dash_closed_runs_nothing(ins):
  match ins:
    case Nil{}:
      {==}
    case +i <> t:
      %Equal.sym(Bool, DashConn.cw_quiet1(DashConn.cs_out(FDa.step(FDa.Live{Da.Closed{}}, i))), True{}, dcrn.q(FDa.get_ev(i))) : {Bool.and(_, DashConn.cw_quiet(DashConn.cs_outs(t, DashConn.cs_st(FDa.step(FDa.Live{Da.Closed{}}, i))))) == True{} : Bool}
      %Equal.sym(FDa.St, DashConn.cs_st(FDa.step(FDa.Live{Da.Closed{}}, i)), FDa.Live{Da.Closed{}}, dcrn.st(FDa.get_ev(i))) : {DashConn.cw_quiet(DashConn.cs_outs(t, _)) == True{} : Bool}
      DashConn.dash_closed_runs_nothing(t)
