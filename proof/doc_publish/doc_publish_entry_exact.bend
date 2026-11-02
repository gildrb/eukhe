# eukhe: the proof of LAW doc_publish_entry_exact
#
# PROOF: the decoder answers Got{q, rest} only after the count's decoder
# answered Got{k, s1} (then the input is put_nat(k, s1), wire_nat_exact,
# and k fits, wire_nat_decoded_fits) and the tag's decoder answered Got{t,
# rest} on s1 (then s1 is put_nat(t, rest)), with t one of the three tags
# (any other is refused). The entry answers a value only for a request
# read whole with nothing left: that input is the spelled request.

import Base
import ../../bend/doc_publish.bend as Dp
import ../../bend/ffi_doc_publish.bend as FDp
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/doc_publish.bend as DocPublish
import ../base/staging.bend as LStg
import ../base/wire_dec.bend as LE
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits

# the decoder's answer is the spelling of what it read, before the rest,
# and its count fits the wire
def dpx.RP(s: String, d: Wr.Dec<FDp.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      match q:
        case FDp.Req{k, se}:
          {s == DocPublish.sp_w_req(k, se, r) : String} & {LawsBase.wire_fits(k) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# the tag after the count k
def dpx.tag(-s: String, +k: Nat, +s1: String, pre: {s == Wr.put_nat(k, s1) : String}, fk: {LawsBase.wire_fits(k) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> dpx.RP(s, FDp.get_req.tag(k, d)):
  match d:
    case Wr.Got{+t, +s2}:
      match t:
        case 0n:
          (LE.dcw.after(s, k, s1, Wr.put_nat(0n, s2), pre, Wire.wire_nat_exact(s1, 0n, s2, ed)), fk)
        case 1n:
          (LE.dcw.after(s, k, s1, Wr.put_nat(1n, s2), pre, Wire.wire_nat_exact(s1, 1n, s2, ed)), fk)
        case 2n:
          (LE.dcw.after(s, k, s1, Wr.put_nat(2n, s2), pre, Wire.wire_nat_exact(s1, 2n, s2, ed)), fk)
        case 3n+j:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# the count at the start
def dpx.rebases(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> dpx.RP(s, FDp.get_req.rebases(d)):
  match d:
    case Wr.Got{+k, +s1}:
      +e = ed
      dpx.tag(s, k, s1, Wire.wire_nat_exact(s, k, s1, e), Wire.wire_nat_decoded_fits(s, k, s1, e), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def dpx.Goal(s: String) -> Type:
  Sigma<&1, &1, Nat, n => Sigma<&1, &1, Dp.Seen, se => {s == DocPublish.sp_w_req(n, se, "") : String} & {LawsBase.wire_fits(n) == True{} : Bool}>>

# a value answered: a request read whole, nothing left
def dpx.top(-s: String, d: Wr.Dec<FDp.Req>, rp: dpx.RP(s, d), ok: {LawsBase.wire_opens_err(FDp.ffi.got(d)) == False{} : Bool}) -> dpx.Goal(s):
  match d:
    case Wr.Got{q, rest}:
      match q:
        case FDp.Req{k, se}:
          match rest:
            case SNil{}:
              (k, (se, rp))
            case SCon{x, y}:
              LStg.stg.absurd(dpx.Goal(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(dpx.Goal(s), ok)

def DocPublish.doc_publish_entry_exact(s, ok):
  dpx.top(s, FDp.get_req(s), dpx.rebases(s, Wr.get_nat(s), {==}), ok)
