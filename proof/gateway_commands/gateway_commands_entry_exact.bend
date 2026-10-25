# eukhe: the proof of LAW gateway_commands_entry_exact
#
# PROOF: each decoder of bend/ffi_gateway_commands.bend answers
# Got{x, rest} only for an input that is the spec's spelling of x before
# rest, with x within the wire (gcx.*: a predicate per decoder answer,
# carried stage by stage with the shared string and list exactness lemmas:
# dcw.str, dcw.strs.list). The entry answers a value only for a request
# read whole with nothing left: that input is the spelled request
# (gcx.top).

import Base
import ../../bend/ffi_gateway_commands.bend as FGc
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/gateway_commands.bend as GatewayCommands
import ../../laws/doc_commit.bend as DocCommit
import ../base/staging.bend as LStg
import ../base/bool.bend as LBool
import ../base/wire_dec.bend as LE
import ../base/wire_strs.bend as LS

def gcx.RP(s: String, d: Wr.Dec<FGc.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == GatewayCommands.gc_w_req(q, r) : String} & {GatewayCommands.gc_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def gcx.sessions(-s: String, +t: String, -s2: String, pre: {s == Wr.put_str(t, s2) : String}, ft: {LawsBase.wire_fits(String.length(t)) == True{} : Bool}, d: Wr.Dec<List<&2, String>>, ls: LS.dcw.strs.LS(s2, d)) -> gcx.RP(s, FGc.get_req.sessions(t, d)):
  match d:
    case Wr.Got{+ns, +r}:
      (e, fs2) = ls
      (fn, fd) = fs2
      (Equal.trans(String, s, Wr.put_str(t, s2), Wr.put_str(t, Wr.put_list(~String, ~Wr.put_str, ns, r)), pre, Equal.cong(String, String, z => Wr.put_str(t, z), s2, Wr.put_list(~String, ~Wr.put_str, ns, r), e)),
        LBool.cb_and_intro(LawsBase.wire_fits(String.length(t)), Bool.and(LawsBase.wire_fits(List.length(&2, String, ns)), DocCommit.sp_fit_strs(ns)), ft, LBool.cb_and_intro(LawsBase.wire_fits(List.length(&2, String, ns)), DocCommit.sp_fit_strs(ns), fn, fd)))
    case Wr.Bad{}:
      Unit{}

def gcx.text(+s: String, d: Wr.Dec<String>, sp: LE.dcw.SP(s, d)) -> gcx.RP(s, FGc.get_req.text(d)):
  match d:
    case Wr.Got{+t, +s2}:
      (e, ft) = sp
      gcx.sessions(s, t, s2, e, ft, Wr.get_list(~String, ~Wr.get_str, s2), LS.dcw.strs.list(s2))
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def gcx.top(-s: String, d: Wr.Dec<FGc.Req>, rp: gcx.RP(s, d), ok: {LawsBase.wire_opens_err(FGc.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FGc.Req, r => {s == GatewayCommands.gc_w_req(r, "") : String} & {GatewayCommands.gc_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FGc.Req, r2 => {s == GatewayCommands.gc_w_req(r2, "") : String} & {GatewayCommands.gc_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FGc.Req, r2 => {s == GatewayCommands.gc_w_req(r2, "") : String} & {GatewayCommands.gc_fit_req(r2) == True{} : Bool}>, ok)

def GatewayCommands.gateway_commands_entry_exact(s, ok):
  gcx.top(s, FGc.get_req(s), gcx.text(s, Wr.get_str(s), LE.dcw.str(s)), ok)
