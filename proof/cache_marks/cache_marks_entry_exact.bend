# eukhe: the proof of LAW cache_marks_entry_exact
#
# PROOF: each decoder stage of bend/ffi_cache_marks.bend answers Got{x,
# rest} only for an input that is the spec's spelling of x before rest,
# with every number of x within the wire (cmx.*: a predicate per decoder
# answer, carried stage by stage with wire_nat_exact, wire_nat_decoded_fits
# and the exactness of a list of Bools, LLog.pe.bools_exact; a count past
# the wire makes the list decoder refuse). The entry answers a value only
# for a request read whole with nothing left: that input is the spelled
# request (cmx.top).

import Base
import ../../bend/cache_marks.bend as Cm
import ../../bend/ffi_cache_marks.bend as FCm
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/cache_marks.bend as CacheMarks
import ../base/staging.bend as LStg
import ../base/bool.bend as LBool
import ../base/wire_dec.bend as LE
import ../log/base.bend as LLog
import ./base.bend as LA

def cmx.RP(s: String, d: Wr.Dec<FCm.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == CacheMarks.sp_w_req(q, r) : String} & {CacheMarks.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def cmx.marked(-s: String, +s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<Nat>, np: LE.dcw.NP(s1, d), ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> cmx.RP(s, FCm.get_req.marked(d)):
  match d:
    case Wr.Got{+n, +r}:
      (LE.dcw.after(s, 0n, s1, Wr.put_nat(n, r), pre, np), Wire.wire_nat_decoded_fits(s1, n, r, ed))
    case Wr.Bad{}:
      Unit{}

# a list decoded from a count past the wire is refused
def cmx.count_fits(b: Bool, +n: Nat, +x: String, -ws: List<&2, Bool>, -r: String, eb: {LawsBase.wire_fits(n) == b : Bool}, ed: {Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_nat(n, x)) == Wr.Got{ws, r} : Wr.Dec<List<&2, Bool>>}) -> {LawsBase.wire_fits(n) == True{} : Bool}:
  match b:
    case True{}:
      eb
    case False{}:
      +c = Equal.trans(Wr.Dec<List<&2, Bool>>, Wr.Got{ws, r}, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_nat(n, x)), Wr.Bad{}, Equal.sym(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_nat(n, x)), Wr.Got{ws, r}, ed), Equal.cong(Wr.Dec<Nat>, Wr.Dec<List<&2, Bool>>, z => Wr.get_list.start(~Bool, ~Wr.get_bool, z), Wr.get_nat(Wr.put_nat(n, x)), Wr.Bad{}, Wire.wire_nat_too_long(n, x, eb)))
      LE.dcw.got_bad(List<&2, Bool>, {LawsBase.wire_fits(n) == True{} : Bool}, ws, r, c)

def cmx.wants(-s: String, +p: Nat, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(p, s2)) : String}, fp: {LawsBase.wire_fits(p) == True{} : Bool}, d: Wr.Dec<List<&2, Bool>>, ed: {Wr.get_list(~Bool, ~Wr.get_bool, s2) == d : Wr.Dec<List<&2, Bool>>}) -> cmx.RP(s, FCm.get_req.wants(p, d)):
  match d:
    case Wr.Got{+ws, +r}:
      +e2 = ed
      +ex = Equal.trans(String, s2, Wr.put_list(~Bool, ~Wr.put_bool, ws, r), Wr.put_nat(List.length(&2, Bool, ws), CacheMarks.sp_w_bools(ws, r)), LLog.pe.bools_exact(s2, ws, r, e2), LA.cmb.put_list(ws, r))
      +ed2 = Equal.trans(Wr.Dec<List<&2, Bool>>, Wr.get_list(~Bool, ~Wr.get_bool, Wr.put_nat(List.length(&2, Bool, ws), CacheMarks.sp_w_bools(ws, r))), Wr.get_list(~Bool, ~Wr.get_bool, s2), Wr.Got{ws, r}, Equal.cong(String, Wr.Dec<List<&2, Bool>>, z => Wr.get_list(~Bool, ~Wr.get_bool, z), Wr.put_nat(List.length(&2, Bool, ws), CacheMarks.sp_w_bools(ws, r)), s2, Equal.sym(String, s2, Wr.put_nat(List.length(&2, Bool, ws), CacheMarks.sp_w_bools(ws, r)), ex)), e2)
      +fn = cmx.count_fits(LawsBase.wire_fits(List.length(&2, Bool, ws)), List.length(&2, Bool, ws), CacheMarks.sp_w_bools(ws, r), ws, r, {==}, ed2)
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_nat(p, s2)), Wr.put_nat(1n, Wr.put_nat(p, Wr.put_nat(List.length(&2, Bool, ws), CacheMarks.sp_w_bools(ws, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_nat(p, z)), s2, Wr.put_nat(List.length(&2, Bool, ws), CacheMarks.sp_w_bools(ws, r)), ex)), LBool.cb_and_intro(LawsBase.wire_fits(p), LawsBase.wire_fits(List.length(&2, Bool, ws)), fp, fn))
    case Wr.Bad{}:
      Unit{}

def cmx.placed(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, np: LE.dcw.NP(s1, d), ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> cmx.RP(s, FCm.get_req.placed(d)):
  match d:
    case Wr.Got{+p, +s2}:
      +e = ed
      cmx.wants(s, p, s2, LE.dcw.after(s, 1n, s1, Wr.put_nat(p, s2), pre, np), Wire.wire_nat_decoded_fits(s1, p, s2, e), Wr.get_list(~Bool, ~Wr.get_bool, s2), {==})
    case Wr.Bad{}:
      Unit{}

def cmx.tag(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> cmx.RP(s, FCm.get_req.tag(d)):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          cmx.marked(s, s1, Wire.wire_nat_exact(s, 0n, s1, ed), Wr.get_nat(s1), LE.dcw.nat(s1), {==})
        case 1n:
          cmx.placed(s, s1, Wire.wire_nat_exact(s, 1n, s1, ed), Wr.get_nat(s1), LE.dcw.nat(s1), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def cmx.top(-s: String, d: Wr.Dec<FCm.Req>, rp: cmx.RP(s, d), ok: {LawsBase.wire_opens_err(FCm.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FCm.Req, r => {s == CacheMarks.sp_w_req(r, "") : String} & {CacheMarks.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FCm.Req, r2 => {s == CacheMarks.sp_w_req(r2, "") : String} & {CacheMarks.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FCm.Req, r2 => {s == CacheMarks.sp_w_req(r2, "") : String} & {CacheMarks.sp_fit_req(r2) == True{} : Bool}>, ok)

def CacheMarks.cache_marks_entry_exact(s, ok):
  cmx.top(s, FCm.get_req(s), cmx.tag(s, Wr.get_nat(s), {==}), ok)
