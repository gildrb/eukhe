# eukhe: the proof of LAW theme_ffi_spelled
# Every decoder stage answers a value only for its spelling, within the
# wire (LTE.tx.req); the entry answers a decision only for a request read
# whole, nothing left (te.top).

import Base
import ../../bend/wire.bend as Wr
import ../../bend/ffi_theme.bend as FTh
import ../../spec/theme/wire.bend as Tw
import ../../laws/base.bend as LawsBase
import ../../laws/theme_entry.bend as ThemeEntry
import ./base.bend as LTE

def te.T(s: String) -> Type:
  Sigma<&1, &1, FTh.Req, q => {s == Tw.req(q, "") : String} & {Tw.fits(q) == True{} : Bool}>

# a decision answered: a request read whole, nothing left
def te.top(-s: String, d: Wr.Dec<FTh.Req>, rp: LTE.tx.RQP(s, d), ok: {LawsBase.wire_opens_err(FTh.run(d)) == False{} : Bool}) -> te.T(s):
  match d:
    case Wr.Got{q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{y, z}:
          LTE.tx.absurd(te.T(s), ok)
    case Wr.Bad{}:
      LTE.tx.absurd(te.T(s), ok)

def ThemeEntry.theme_ffi_spelled(s, ok):
  te.top(s, FTh.get_req.go(Wr.get_nat(s)), LTE.tx.req(s, Wr.get_nat(s), {==}), ok)
