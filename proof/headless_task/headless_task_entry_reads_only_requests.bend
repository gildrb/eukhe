# eukhe: the proof of LAW headless_task_entry_reads_only_requests
#
# PROOF: each decoder stage of bend/ffi_headless_task.bend answers Got{x,
# rest} only for an input that spells x before rest (hto.*: a predicate
# per stage, carried with wire_nat_exact, wire_bool_exact, the tags each
# stage accepts and the reason stage of the headless_exit proof, hxo.*);
# a value is answered only for a request read whole, with nothing left
# (hto.top).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/headless_task.bend as Ht
import ../../bend/ffi_headless_exit.bend as FHx
import ../../bend/ffi_headless_task.bend as FHt
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/headless_task.bend as HeadlessTask
import ../../spec/durable/headless_wire.bend as SpW
import ../../spec/durable/headless_task.bend as SpT
import ../base/staging.bend as LStg
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../headless_exit/headless_exit_entry_reads_only_requests.bend as PHxo

# The cause, the reading
# ----------------------

def hto.CT(s: String, x: Wr.Dec<Hx.Cause>) -> Type:
  match x:
    case Wr.Got{c, rr}:
      {s == SpW.w_cause(c, rr) : String}
    case Wr.Bad{}:
      Unit

def hto.failed(-s: String, +s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, x: Wr.Dec<Hx.Reason>, rr: PHxo.hxo.RR(s1, x)) -> hto.CT(s, FHt.get_cause.failed(x)):
  match x:
    case Wr.Got{+r, +s2}:
      Equal.trans(String, s, Wr.put_nat(3n, s1), Wr.put_nat(3n, SpW.w_reason(r, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(3n, z), s1, SpW.w_reason(r, s2), rr))
    case Wr.Bad{}:
      Unit{}

def hto.cause_tag(-s: String, t: Nat, +s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> hto.CT(s, FHt.get_cause(Wr.Got{t, s1})):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n:
      e
    case 3n:
      hto.failed(s, s1, e, FHx.get_reason(Wr.get_nat(s1)), PHxo.hxo.reason(s1, Wr.get_nat(s1), {==}))
    case 4n:
      e
    case 5n:
      e
    case 6n:
      e
    case 7n:
      e
    case 8n:
      e
    case 9n:
      e
    case 10n:
      e
    case 11n+u:
      Unit{}

def hto.cause(+s: String, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == x : Wr.Dec<Nat>}) -> hto.CT(s, FHt.get_cause(x)):
  match x:
    case Wr.Got{+t, +s1}:
      +e = ed
      hto.cause_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, e))
    case Wr.Bad{}:
      Unit{}

def hto.RT(s: String, x: Wr.Dec<Ht.Report>) -> Type:
  match x:
    case Wr.Got{r, rr}:
      {s == SpT.w_report(r, rr) : String}
    case Wr.Bad{}:
      Unit

def hto.report_tag(-s: String, t: Nat, -s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> hto.RT(s, FHt.get_report(Wr.Got{t, s1})):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n:
      e
    case 3n:
      e
    case 4n+u:
      Unit{}

def hto.report(+s: String, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == x : Wr.Dec<Nat>}) -> hto.RT(s, FHt.get_report(x)):
  match x:
    case Wr.Got{+t, +s1}:
      +e = ed
      hto.report_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, e))
    case Wr.Bad{}:
      Unit{}

# The request
# -----------

def hto.RP(s: String, x: Wr.Dec<Ht.Facts>) -> Type:
  match x:
    case Wr.Got{f, rr}:
      {s == SpT.w_task_req(f, rr) : String}
    case Wr.Bad{}:
      Unit

def hto.after_acted(-s: String, +c: Hx.Cause, +a: Bool, +s2: String, pre: {s == SpW.w_cause(c, Wr.put_bool(a, s2)) : String}, x: Wr.Dec<Ht.Report>, rt: hto.RT(s2, x)) -> hto.RP(s, FHt.get_facts.report(c, a, x)):
  match x:
    case Wr.Got{+r, +s3}:
      Equal.trans(String, s, SpW.w_cause(c, Wr.put_bool(a, s2)), SpW.w_cause(c, Wr.put_bool(a, SpT.w_report(r, s3))), pre, Equal.cong(String, String, z => SpW.w_cause(c, Wr.put_bool(a, z)), s2, SpT.w_report(r, s3), rt))
    case Wr.Bad{}:
      Unit{}

def hto.after_cause(-s: String, +c: Hx.Cause, +s1: String, pre: {s == SpW.w_cause(c, s1) : String}, x: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == x : Wr.Dec<Bool>}) -> hto.RP(s, FHt.get_facts.acted(c, x)):
  match x:
    case Wr.Got{+a, +s2}:
      +e = ed
      +pre2 = Equal.trans(String, s, SpW.w_cause(c, s1), SpW.w_cause(c, Wr.put_bool(a, s2)), pre, Equal.cong(String, String, z => SpW.w_cause(c, z), s1, Wr.put_bool(a, s2), Wire.wire_bool_exact(s1, a, s2, e)))
      hto.after_acted(s, c, a, s2, pre2, FHt.get_report(Wr.get_nat(s2)), hto.report(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def hto.after_reason(-s: String, x: Wr.Dec<Hx.Cause>, ct: hto.CT(s, x)) -> hto.RP(s, FHt.get_facts.cause(x)):
  match x:
    case Wr.Got{+c, +s1}:
      hto.after_cause(s, c, s1, ct, Wr.get_bool(s1), {==})
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled
def hto.req(+s: String) -> hto.RP(s, FHt.get_facts(s)):
  hto.after_reason(s, FHt.get_cause(Wr.get_nat(s)), hto.cause(s, Wr.get_nat(s), {==}))

def hto.T(s: String) -> Type:
  Sigma<&1, &1, Ht.Facts, f => {s == SpT.w_task_req(f, "") : String}>

# a value answered: a request read whole, nothing left
def hto.top(-s: String, x: Wr.Dec<Ht.Facts>, rp: hto.RP(s, x), ok: {LawsBase.wire_opens_err(FHt.ffi.got(x)) == False{} : Bool}) -> hto.T(s):
  match x:
    case Wr.Got{+f, rest}:
      match rest:
        case SNil{}:
          (f, rp)
        case SCon{y, z}:
          LStg.stg.absurd(hto.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(hto.T(s), ok)

def HeadlessTask.headless_task_entry_reads_only_requests(s, ok):
  hto.top(s, FHt.get_facts(s), hto.req(s), ok)
