# eukhe: the proof of LAW headless_exit_entry_reads_only_requests
#
# PROOF: each decoder stage of bend/ffi_headless_exit.bend answers Got{x,
# rest} only for an input that spells x before rest (hxo.*: a predicate
# per stage, carried with wire_nat_exact and wire_bool_exact and the tags
# each stage accepts); a value is answered only for a request read whole,
# with nothing left (hxo.top).

import Base
import ../../bend/headless_exit.bend as Hx
import ../../bend/ffi_headless_exit.bend as FHx
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/headless_exit.bend as HeadlessExit
import ../../spec/durable/headless_wire.bend as SpW
import ../base/staging.bend as LStg
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact

# The wait, the reason, the run, the terminal entry
# -------------------------------------------------

def hxo.WT(s: String, x: Wr.Dec<Hx.Wait>) -> Type:
  match x:
    case Wr.Got{w, rr}:
      {s == SpW.w_wait(w, rr) : String}
    case Wr.Bad{}:
      Unit

def hxo.wait_tag(-s: String, t: Nat, -s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> hxo.WT(s, FHx.get_wait(Wr.Got{t, s1})):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n:
      e
    case 3n+u:
      Unit{}

def hxo.wait(+s: String, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == x : Wr.Dec<Nat>}) -> hxo.WT(s, FHx.get_wait(x)):
  match x:
    case Wr.Got{+t, +s1}:
      +e = ed
      hxo.wait_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, e))
    case Wr.Bad{}:
      Unit{}

def hxo.RR(s: String, x: Wr.Dec<Hx.Reason>) -> Type:
  match x:
    case Wr.Got{r, rr}:
      {s == SpW.w_reason(r, rr) : String}
    case Wr.Bad{}:
      Unit

def hxo.reason_tag(-s: String, t: Nat, -s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> hxo.RR(s, FHx.get_reason(Wr.Got{t, s1})):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n:
      e
    case 3n:
      e
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

def hxo.reason(+s: String, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == x : Wr.Dec<Nat>}) -> hxo.RR(s, FHx.get_reason(x)):
  match x:
    case Wr.Got{+t, +s1}:
      +e = ed
      hxo.reason_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, e))
    case Wr.Bad{}:
      Unit{}

def hxo.RN(s: String, x: Wr.Dec<Hx.Run>) -> Type:
  match x:
    case Wr.Got{run, rr}:
      {s == SpW.w_run(run, rr) : String}
    case Wr.Bad{}:
      Unit

def hxo.run_reason(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, x: Wr.Dec<Hx.Reason>, rr: hxo.RR(s1, x)) -> hxo.RN(s, FHx.get_run.reason(x)):
  match x:
    case Wr.Got{+r, +s2}:
      Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, SpW.w_reason(r, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, SpW.w_reason(r, s2), rr))
    case Wr.Bad{}:
      Unit{}

def hxo.run_tag(-s: String, t: Nat, +s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> hxo.RN(s, FHx.get_run(Wr.Got{t, s1})):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n:
      hxo.run_reason(s, s1, e, FHx.get_reason(Wr.get_nat(s1)), hxo.reason(s1, Wr.get_nat(s1), {==}))
    case 3n+u:
      Unit{}

def hxo.run(+s: String, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == x : Wr.Dec<Nat>}) -> hxo.RN(s, FHx.get_run(x)):
  match x:
    case Wr.Got{+t, +s1}:
      +e = ed
      hxo.run_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, e))
    case Wr.Bad{}:
      Unit{}

def hxo.PR(s: String, x: Wr.Dec<Hx.Primary>) -> Type:
  match x:
    case Wr.Got{p, rr}:
      {s == SpW.w_primary(p, rr) : String}
    case Wr.Bad{}:
      Unit

def hxo.primary_tag(-s: String, t: Nat, -s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> hxo.PR(s, FHx.get_primary(Wr.Got{t, s1})):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n:
      e
    case 3n:
      e
    case 4n:
      e
    case 5n:
      e
    case 6n:
      e
    case 7n:
      e
    case 8n+u:
      Unit{}

def hxo.primary(+s: String, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == x : Wr.Dec<Nat>}) -> hxo.PR(s, FHx.get_primary(x)):
  match x:
    case Wr.Got{+t, +s1}:
      +e = ed
      hxo.primary_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, e))
    case Wr.Bad{}:
      Unit{}

# The request
# -----------

def hxo.RP(s: String, x: Wr.Dec<Hx.Facts>) -> Type:
  match x:
    case Wr.Got{f, rr}:
      {s == SpW.w_exit_req(f, rr) : String}
    case Wr.Bad{}:
      Unit

def hxo.budget(-s: String, +cf: Bool, +w: Hx.Wait, +run: Hx.Run, +p: Hx.Primary, +c: Bool, +a: Bool, +s6: String, pre: {s == Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, SpW.w_primary(p, Wr.put_bool(c, Wr.put_bool(a, s6)))))) : String}, x: Wr.Dec<Bool>, ed: {Wr.get_bool(s6) == x : Wr.Dec<Bool>}) -> hxo.RP(s, FHx.get_facts.budget(cf, w, run, p, c, a, x)):
  match x:
    case Wr.Got{+ba, +s7}:
      +e = ed
      Equal.trans(String, s, Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, SpW.w_primary(p, Wr.put_bool(c, Wr.put_bool(a, s6)))))), Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, SpW.w_primary(p, Wr.put_bool(c, Wr.put_bool(a, Wr.put_bool(ba, s7))))))), pre, Equal.cong(String, String, z => Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, SpW.w_primary(p, Wr.put_bool(c, Wr.put_bool(a, z)))))), s6, Wr.put_bool(ba, s7), Wire.wire_bool_exact(s6, ba, s7, e)))
    case Wr.Bad{}:
      Unit{}

def hxo.auto(-s: String, +cf: Bool, +w: Hx.Wait, +run: Hx.Run, +p: Hx.Primary, +c: Bool, +s5: String, pre: {s == Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, SpW.w_primary(p, Wr.put_bool(c, s5))))) : String}, x: Wr.Dec<Bool>, ed: {Wr.get_bool(s5) == x : Wr.Dec<Bool>}) -> hxo.RP(s, FHx.get_facts.auto(cf, w, run, p, c, x)):
  match x:
    case Wr.Got{+a, +s6}:
      +e = ed
      +pre2 = Equal.trans(String, s, Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, SpW.w_primary(p, Wr.put_bool(c, s5))))), Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, SpW.w_primary(p, Wr.put_bool(c, Wr.put_bool(a, s6)))))), pre, Equal.cong(String, String, z => Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, SpW.w_primary(p, Wr.put_bool(c, z))))), s5, Wr.put_bool(a, s6), Wire.wire_bool_exact(s5, a, s6, e)))
      hxo.budget(s, cf, w, run, p, c, a, s6, pre2, Wr.get_bool(s6), {==})
    case Wr.Bad{}:
      Unit{}

def hxo.comp(-s: String, +cf: Bool, +w: Hx.Wait, +run: Hx.Run, +p: Hx.Primary, +s4: String, pre: {s == Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, SpW.w_primary(p, s4)))) : String}, x: Wr.Dec<Bool>, ed: {Wr.get_bool(s4) == x : Wr.Dec<Bool>}) -> hxo.RP(s, FHx.get_facts.comp(cf, w, run, p, x)):
  match x:
    case Wr.Got{+c, +s5}:
      +e = ed
      +pre2 = Equal.trans(String, s, Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, SpW.w_primary(p, s4)))), Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, SpW.w_primary(p, Wr.put_bool(c, s5))))), pre, Equal.cong(String, String, z => Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, SpW.w_primary(p, z)))), s4, Wr.put_bool(c, s5), Wire.wire_bool_exact(s4, c, s5, e)))
      hxo.auto(s, cf, w, run, p, c, s5, pre2, Wr.get_bool(s5), {==})
    case Wr.Bad{}:
      Unit{}

def hxo.after_run(-s: String, +cf: Bool, +w: Hx.Wait, +run: Hx.Run, +s3: String, pre: {s == Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, s3))) : String}, x: Wr.Dec<Hx.Primary>, pr: hxo.PR(s3, x)) -> hxo.RP(s, FHx.get_facts.primary(cf, w, run, x)):
  match x:
    case Wr.Got{+p, +s4}:
      +pre2 = Equal.trans(String, s, Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, s3))), Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, SpW.w_primary(p, s4)))), pre, Equal.cong(String, String, z => Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, z))), s3, SpW.w_primary(p, s4), pr))
      hxo.comp(s, cf, w, run, p, s4, pre2, Wr.get_bool(s4), {==})
    case Wr.Bad{}:
      Unit{}

def hxo.after_wait(-s: String, +cf: Bool, +w: Hx.Wait, +s2: String, pre: {s == Wr.put_bool(cf, SpW.w_wait(w, s2)) : String}, x: Wr.Dec<Hx.Run>, rn: hxo.RN(s2, x)) -> hxo.RP(s, FHx.get_facts.run(cf, w, x)):
  match x:
    case Wr.Got{+run, +s3}:
      +pre2 = Equal.trans(String, s, Wr.put_bool(cf, SpW.w_wait(w, s2)), Wr.put_bool(cf, SpW.w_wait(w, SpW.w_run(run, s3))), pre, Equal.cong(String, String, z => Wr.put_bool(cf, SpW.w_wait(w, z)), s2, SpW.w_run(run, s3), rn))
      hxo.after_run(s, cf, w, run, s3, pre2, FHx.get_primary(Wr.get_nat(s3)), hxo.primary(s3, Wr.get_nat(s3), {==}))
    case Wr.Bad{}:
      Unit{}

def hxo.after_command(-s: String, +cf: Bool, +s1: String, pre: {s == Wr.put_bool(cf, s1) : String}, x: Wr.Dec<Hx.Wait>, wt: hxo.WT(s1, x)) -> hxo.RP(s, FHx.get_facts.wait(cf, x)):
  match x:
    case Wr.Got{+w, +s2}:
      +pre2 = Equal.trans(String, s, Wr.put_bool(cf, s1), Wr.put_bool(cf, SpW.w_wait(w, s2)), pre, Equal.cong(String, String, z => Wr.put_bool(cf, z), s1, SpW.w_wait(w, s2), wt))
      hxo.after_wait(s, cf, w, s2, pre2, FHx.get_run(Wr.get_nat(s2)), hxo.run(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def hxo.command(+s: String, x: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == x : Wr.Dec<Bool>}) -> hxo.RP(s, FHx.get_facts.command(x)):
  match x:
    case Wr.Got{+cf, +s1}:
      +e = ed
      hxo.after_command(s, cf, s1, Wire.wire_bool_exact(s, cf, s1, e), FHx.get_wait(Wr.get_nat(s1)), hxo.wait(s1, Wr.get_nat(s1), {==}))
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled
def hxo.req(+s: String) -> hxo.RP(s, FHx.get_facts(s)):
  hxo.command(s, Wr.get_bool(s), {==})

def hxo.T(s: String) -> Type:
  Sigma<&1, &1, Hx.Facts, f => {s == SpW.w_exit_req(f, "") : String}>

# a value answered: a request read whole, nothing left
def hxo.top(-s: String, x: Wr.Dec<Hx.Facts>, rp: hxo.RP(s, x), ok: {LawsBase.wire_opens_err(FHx.ffi.got(x)) == False{} : Bool}) -> hxo.T(s):
  match x:
    case Wr.Got{+f, rest}:
      match rest:
        case SNil{}:
          (f, rp)
        case SCon{y, z}:
          LStg.stg.absurd(hxo.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(hxo.T(s), ok)

def HeadlessExit.headless_exit_entry_reads_only_requests(s, ok):
  hxo.top(s, FHx.get_facts(s), hxo.req(s), ok)
