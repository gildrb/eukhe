# eukhe: the proof of LAW thread_entry_exact
#
# PROOF: the entry's decoder answers Got{q, rest} only after the list
# decoder answered Got{ns, rest}: then the input is the list encoder's
# spelling of ns before rest (wire_list_exact), the spec's spelling
# (wire_nats_spells), and ns fits the wire (ge.nats_fit); a list of fewer
# than two Nats is refused, and a longer one is through, verbatim and the
# starts (tex.of). The entry answers a value only for a request read
# whole with nothing left: that input is the spelled request (tex.top).

import Base
import ../../bend/ffi_thread.bend as FTh
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/thread.bend as Thread
import ../wire/wire_list_exact.bend as PWireListExact
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ../glob/base/entry.bend as LGlobEntry
import ./base.bend as LA

def tex.RP(s: String, d: Wr.Dec<FTh.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Thread.sp_w_req(q, r) : String} & {Thread.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def tex.of(-s: String, ns: List<&2, Nat>, +r: String, pre: {s == Wr.put_list(~Nat, ~Wr.put_nat, ns, r) : String}, fit: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ns)), LawsBase.wire_nats_fit(ns)) == True{} : Bool}) -> tex.RP(s, FTh.get_req.of(ns, r)):
  match ns:
    case Nil{}:
      Unit{}
    case +t <> more:
      match more:
        case Nil{}:
          Unit{}
        case +v <> +xs:
          (Equal.trans(String, s, Wr.put_list(~Nat, ~Wr.put_nat, t <> v <> xs, r), LawsBase.wire_spell_nats(t <> v <> xs, r), pre, Wire.wire_nats_spells(t <> v <> xs, r)), fit)

def tex.got(+s: String, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s) == d : Wr.Dec<List<&2, Nat>>}) -> tex.RP(s, FTh.get_req.got(d)):
  match d:
    case Wr.Got{+ns, +r}:
      +e = ed
      tex.of(s, ns, r, Wire.wire_list_exact(s, ns, r, e), LGlobEntry.ge.nats_fit(s, ns, r, e))
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def tex.top(-s: String, d: Wr.Dec<FTh.Req>, rp: tex.RP(s, d), ok: {LawsBase.wire_opens_err(FTh.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FTh.Req, r => {s == Thread.sp_w_req(r, "") : String} & {Thread.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LA.thb.absurd_tf(Sigma<&1, &1, FTh.Req, r2 => {s == Thread.sp_w_req(r2, "") : String} & {Thread.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LA.thb.absurd_tf(Sigma<&1, &1, FTh.Req, r2 => {s == Thread.sp_w_req(r2, "") : String} & {Thread.sp_fit_req(r2) == True{} : Bool}>, ok)

def Thread.thread_entry_exact(s, ok):
  tex.top(s, FTh.get_req(s), tex.got(s, Wr.get_list(~Nat, ~Wr.get_nat, s), {==}), ok)
