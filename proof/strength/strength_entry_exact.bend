# eukhe: the proof of LAW strength_entry_exact
#
# PROOF: the decoder answers Got{q, rest} only for an input that is the
# spelling of q before rest, every number and count within the wire
# (SX.sx.req, stage by stage); the entry answers a decision only for a
# request read whole with nothing left (sxe.top).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/ffi_strength.bend as FS
import ../../bend/wire.bend as Wr
import ../../spec/verified/strength_wire.bend as SW
import ../../laws/base.bend as LawsBase
import ../../laws/strength.bend as Strength
import ./base/exact.bend as SX

def sxe.top(-s: String, d: Wr.Dec<FS.Req>, rp: SX.sx.QP(s, d), ok: {LawsBase.wire_opens_err(FS.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FS.Req, v => {s == SW.w_req(v, "") : String} & {SW.fit_req(v) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          SX.sx.absurdT(Sigma<&1, &1, FS.Req, v2 => {s == SW.w_req(v2, "") : String} & {SW.fit_req(v2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      SX.sx.absurdT(Sigma<&1, &1, FS.Req, v2 => {s == SW.w_req(v2, "") : String} & {SW.fit_req(v2) == True{} : Bool}>, ok)

def Strength.strength_entry_exact(s, ok):
  sxe.top(s, FS.get_req(Wr.get_nat(s)), SX.sx.req(s), ok)
