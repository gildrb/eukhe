# eukhe: the proof of LAW attack_entry_exact
#
# PROOF: the decoder answers Got{q, rest} only for an input that is the
# spelling of q before rest, every number and count within the wire
# (LX.axe.req, stage by stage); the entry answers a decision only for a
# request read whole with nothing left (axe.top).

import Base
import ../../bend/verify.bend as V
import ../../bend/strength.bend as St
import ../../bend/attack.bend as At
import ../../bend/ffi_attack.bend as FA
import ../../bend/wire.bend as Wr
import ../../spec/verified/attack_wire.bend as SAW
import ../../laws/base.bend as LawsBase
import ../../laws/attack.bend as Attack
import ./base/entry.bend as LE
import ../strength/base/exact.bend as SX
import ./base/exact.bend as LX

def axe.top(-s: String, d: Wr.Dec<FA.Req>, rp: LX.axe.QP(s, d), ok: {LawsBase.wire_opens_err(FA.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FA.Req, v => {s == SAW.w_req(v, "") : String} & {SAW.fit_req(v) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          SX.sx.absurdT(Sigma<&1, &1, FA.Req, v2 => {s == SAW.w_req(v2, "") : String} & {SAW.fit_req(v2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      SX.sx.absurdT(Sigma<&1, &1, FA.Req, v2 => {s == SAW.w_req(v2, "") : String} & {SAW.fit_req(v2) == True{} : Bool}>, ok)

def Attack.attack_entry_exact(s, ok):
  axe.top(s, FA.get_req(Wr.get_nat(s)), LX.axe.req(s), ok)
