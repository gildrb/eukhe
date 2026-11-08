# eukhe: the proof of LAW tool_result_entry_exact
#
# PROOF: each decoder stage of bend/ffi_tool_result.bend answers Got{x,
# rest} only for an input that is the spec's spelling of x before rest,
# with the count of x within the wire (trx.*: a predicate per decoder
# answer, carried stage by stage with wire_bool_exact and the exactness of
# a list of Bools, LLog.pe.bools_exact; a count past the wire makes the
# list decoder refuse). The entry answers a value only for a request read
# whole with nothing left: that input is the spelled request (trx.top).

import Base
import ../../bend/tool_result.bend as Tr
import ../../bend/ffi_tool_result.bend as FTr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/tool_result.bend as ToolResult
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../base/staging.bend as LStg
import ../base/wire_dec.bend as LE
import ../log/base.bend as LLog
import ./base.bend as LA

def trx.RP(s: String, d: Wr.Dec<FTr.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ToolResult.sp_w_req(q, r) : String} & {ToolResult.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a list decoded from a count past the wire is refused
def trx.count_fits(b: Bool, +n: Nat, +x: String, -ks: List<&2, Bool>, -r: String, eb: {LawsBase.wire_fits(n) == b : Bool}, ed: {Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_nat(n, x)) == Wr.Got{ks, r} : Wr.Dec<List<&2, Bool>>}) -> {LawsBase.wire_fits(n) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +c = Equal.trans(Wr.Dec<List<&2, Bool>>, Wr.Got{ks, r}, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_nat(n, x)), Wr.Bad{}, Equal.sym(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_nat(n, x)), Wr.Got{ks, r}, ed), Equal.cong(Wr.Dec<Nat>, Wr.Dec<List<&2, Bool>>, z => Wr.get_list.start(~Bool, ~Wr.get_bool, z), Wr.get_nat(Wr.put_nat(n, x)), Wr.Bad{}, Wire.wire_nat_too_long(n, x, eb)))
      LE.dcw.got_bad(List<&2, Bool>, {LawsBase.wire_fits(n) == True{} : Bool}, ks, r, c)

def trx.imgs(-s: String, +e: Bool, +s2: String, pre: {s == Wr.put_bool(e, s2) : String}, d: Wr.Dec<List<&2, Bool>>, ed: {Wr.get_list(~Bool, ~Wr.get_bool, s2) == d : Wr.Dec<List<&2, Bool>>}) -> trx.RP(s, FTr.get_req.imgs(e, d)):
  match d:
    case Wr.Got{+ks, +r}:
      +e2 = ed
      +sp = Wr.put_nat(List.length(&2, Bool, ks), ToolResult.sp_w_bools(ks, r))
      +ex = Equal.trans(String, s2, Wr.put_list(~Bool, ~Wr.put_bool, ks, r), sp, LLog.pe.bools_exact(s2, ks, r, e2), LA.trb.put_list(ks, r))
      +ed2 = Equal.trans(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, sp), Wr.get_list(~Bool, ~Wr.get_bool, s2), Wr.Got{ks, r}, Equal.cong(String, Wr.Dec<List<&2, Bool>>, z => Wr.get_list(~Bool, ~Wr.get_bool, z), sp, s2, Equal.sym(String, s2, sp, ex)), e2)
      +fn = trx.count_fits(LawsBase.wire_fits(List.length(&2, Bool, ks)), List.length(&2, Bool, ks), ToolResult.sp_w_bools(ks, r), ks, r, {==}, ed2)
      (Equal.trans(String, s, Wr.put_bool(e, s2), Wr.put_bool(e, sp), pre, Equal.cong(String, String, z => Wr.put_bool(e, z), s2, sp, ex)), fn)
    case Wr.Bad{}:
      Unit{}

def trx.err(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> trx.RP(s, FTr.get_req.err(d)):
  match d:
    case Wr.Got{+e, +s2}:
      trx.imgs(s, e, s2, Wire.wire_bool_exact(s, e, s2, ed), Wr.get_list(~Bool, ~Wr.get_bool, s2), {==})
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def trx.top(-s: String, d: Wr.Dec<FTr.Req>, rp: trx.RP(s, d), ok: {LawsBase.wire_opens_err(FTr.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FTr.Req, r => {s == ToolResult.sp_w_req(r, "") : String} & {ToolResult.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FTr.Req, r2 => {s == ToolResult.sp_w_req(r2, "") : String} & {ToolResult.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FTr.Req, r2 => {s == ToolResult.sp_w_req(r2, "") : String} & {ToolResult.sp_fit_req(r2) == True{} : Bool}>, ok)

def ToolResult.tool_result_entry_exact(s, ok):
  trx.top(s, FTr.get_req(s), trx.err(s, Wr.get_bool(s), {==}), ok)
