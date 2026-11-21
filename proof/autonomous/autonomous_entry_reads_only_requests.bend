# eukhe: the proof of LAW autonomous_entry_reads_only_requests
#
# PROOF: each decoder stage of bend/ffi_autonomous.bend answers Got{x,
# rest} only for an input that spells x before rest (auo.*: a predicate
# per stage, carried with wire_bool_exact, wire_nat_exact and the tags
# each stage accepts); a step is answered only for a request read whole,
# with nothing left (auo.top).

import Base
import ../../bend/verify.bend as V
import ../../bend/autonomous.bend as Au
import ../../bend/ffi_autonomous.bend as FAu
import ../../bend/work_left.bend as Wl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/autonomous.bend as Autonomous
import ../../spec/autonomous/autonomous.bend as SpA
import ../../spec/agents/work_left.bend as SpL
import ../base/staging.bend as LStg
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact

# The answer, the label, the checks, the budget, the reading
# ---------------------------------------------

def auo.AT(s: String, x: Wr.Dec<Au.Answer>) -> Type:
  match x:
    case Wr.Got{a, rr}:
      {s == SpA.w_answer(a, rr) : String}
    case Wr.Bad{}:
      Unit

def auo.answer_tag(-s: String, t: Nat, -s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> auo.AT(s, FAu.get_answer(Wr.Got{t, s1})):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n+u:
      Unit{}

def auo.answer(+s: String, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == x : Wr.Dec<Nat>}) -> auo.AT(s, FAu.get_answer(x)):
  match x:
    case Wr.Got{+t, +s1}:
      +e = ed
      auo.answer_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, e))
    case Wr.Bad{}:
      Unit{}

def auo.LT(s: String, x: Wr.Dec<V.Label>) -> Type:
  match x:
    case Wr.Got{l, rr}:
      {s == SpA.w_label(l, rr) : String}
    case Wr.Bad{}:
      Unit

def auo.label_tag(-s: String, t: Nat, -s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> auo.LT(s, FAu.get_label(Wr.Got{t, s1})):
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

def auo.label(+s: String, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == x : Wr.Dec<Nat>}) -> auo.LT(s, FAu.get_label(x)):
  match x:
    case Wr.Got{+t, +s1}:
      +e = ed
      auo.label_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, e))
    case Wr.Bad{}:
      Unit{}

def auo.CT(s: String, x: Wr.Dec<Au.Checks>) -> Type:
  match x:
    case Wr.Got{c, rr}:
      {s == SpA.w_checks(c, rr) : String}
    case Wr.Bad{}:
      Unit

def auo.ended(-s: String, +s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, x: Wr.Dec<V.Label>, lt: auo.LT(s1, x)) -> auo.CT(s, FAu.get_checks.ended(x)):
  match x:
    case Wr.Got{+l, +s2}:
      Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, SpA.w_label(l, s2)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, SpA.w_label(l, s2), lt))
    case Wr.Bad{}:
      Unit{}

def auo.checks_tag(-s: String, t: Nat, +s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> auo.CT(s, FAu.get_checks(Wr.Got{t, s1})):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n:
      auo.ended(s, s1, e, FAu.get_label(Wr.get_nat(s1)), auo.label(s1, Wr.get_nat(s1), {==}))
    case 3n+u:
      Unit{}

def auo.checks(+s: String, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == x : Wr.Dec<Nat>}) -> auo.CT(s, FAu.get_checks(x)):
  match x:
    case Wr.Got{+t, +s1}:
      +e = ed
      auo.checks_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, e))
    case Wr.Bad{}:
      Unit{}

def auo.BT(s: String, x: Wr.Dec<Au.Budget>) -> Type:
  match x:
    case Wr.Got{b, rr}:
      {s == SpA.w_budget(b, rr) : String}
    case Wr.Bad{}:
      Unit

def auo.budget_tag(-s: String, t: Nat, -s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> auo.BT(s, FAu.get_budget(Wr.Got{t, s1})):
  match t:
    case 0n:
      e
    case 1n:
      e
    case 2n+u:
      Unit{}

def auo.budget(+s: String, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == x : Wr.Dec<Nat>}) -> auo.BT(s, FAu.get_budget(x)):
  match x:
    case Wr.Got{+t, +s1}:
      +e = ed
      auo.budget_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, e))
    case Wr.Bad{}:
      Unit{}

def auo.RdT(s: String, x: Wr.Dec<Wl.Reading>) -> Type:
  match x:
    case Wr.Got{r, rr}:
      {s == SpL.w_reading(r, rr) : String}
    case Wr.Bad{}:
      Unit

def auo.reading_tag(-s: String, t: Nat, -s1: String, e: {s == Wr.put_nat(t, s1) : String}) -> auo.RdT(s, FAu.get_reading(Wr.Got{t, s1})):
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

def auo.reading(+s: String, x: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == x : Wr.Dec<Nat>}) -> auo.RdT(s, FAu.get_reading(x)):
  match x:
    case Wr.Got{+t, +s1}:
      +e = ed
      auo.reading_tag(s, t, s1, Wire.wire_nat_exact(s, t, s1, e))
    case Wr.Bad{}:
      Unit{}

# The request
# -----------

def auo.RP(s: String, x: Wr.Dec<Au.Facts>) -> Type:
  match x:
    case Wr.Got{f, rr}:
      {s == SpA.w_req(f, rr) : String}
    case Wr.Bad{}:
      Unit

def auo.after_reading(-s: String, +on: Bool, +a: Au.Answer, +c: Au.Checks, +b: Au.Budget, +s4: String, pre: {s == Wr.put_bool(on, SpA.w_answer(a, SpA.w_checks(c, SpA.w_budget(b, s4)))) : String}, x: Wr.Dec<Wl.Reading>, rt: auo.RdT(s4, x)) -> auo.RP(s, FAu.get_facts.reading(on, a, c, b, x)):
  match x:
    case Wr.Got{+r, +s5}:
      Equal.trans(String, s, Wr.put_bool(on, SpA.w_answer(a, SpA.w_checks(c, SpA.w_budget(b, s4)))), Wr.put_bool(on, SpA.w_answer(a, SpA.w_checks(c, SpA.w_budget(b, SpL.w_reading(r, s5))))), pre, Equal.cong(String, String, z => Wr.put_bool(on, SpA.w_answer(a, SpA.w_checks(c, SpA.w_budget(b, z)))), s4, SpL.w_reading(r, s5), rt))
    case Wr.Bad{}:
      Unit{}

def auo.after_budget(-s: String, +on: Bool, +a: Au.Answer, +c: Au.Checks, +s3: String, pre: {s == Wr.put_bool(on, SpA.w_answer(a, SpA.w_checks(c, s3))) : String}, x: Wr.Dec<Au.Budget>, bt: auo.BT(s3, x)) -> auo.RP(s, FAu.get_facts.budget(on, a, c, x)):
  match x:
    case Wr.Got{+b, +s4}:
      +pre2 = Equal.trans(String, s, Wr.put_bool(on, SpA.w_answer(a, SpA.w_checks(c, s3))), Wr.put_bool(on, SpA.w_answer(a, SpA.w_checks(c, SpA.w_budget(b, s4)))), pre, Equal.cong(String, String, z => Wr.put_bool(on, SpA.w_answer(a, SpA.w_checks(c, z))), s3, SpA.w_budget(b, s4), bt))
      auo.after_reading(s, on, a, c, b, s4, pre2, FAu.get_reading(Wr.get_nat(s4)), auo.reading(s4, Wr.get_nat(s4), {==}))
    case Wr.Bad{}:
      Unit{}

def auo.after_checks(-s: String, +on: Bool, +a: Au.Answer, +s2: String, pre: {s == Wr.put_bool(on, SpA.w_answer(a, s2)) : String}, x: Wr.Dec<Au.Checks>, ct: auo.CT(s2, x)) -> auo.RP(s, FAu.get_facts.checks(on, a, x)):
  match x:
    case Wr.Got{+c, +s3}:
      +pre2 = Equal.trans(String, s, Wr.put_bool(on, SpA.w_answer(a, s2)), Wr.put_bool(on, SpA.w_answer(a, SpA.w_checks(c, s3))), pre, Equal.cong(String, String, z => Wr.put_bool(on, SpA.w_answer(a, z)), s2, SpA.w_checks(c, s3), ct))
      auo.after_budget(s, on, a, c, s3, pre2, FAu.get_budget(Wr.get_nat(s3)), auo.budget(s3, Wr.get_nat(s3), {==}))
    case Wr.Bad{}:
      Unit{}

def auo.after_answer(-s: String, +on: Bool, +s1: String, pre: {s == Wr.put_bool(on, s1) : String}, x: Wr.Dec<Au.Answer>, at: auo.AT(s1, x)) -> auo.RP(s, FAu.get_facts.answer(on, x)):
  match x:
    case Wr.Got{+a, +s2}:
      +pre2 = Equal.trans(String, s, Wr.put_bool(on, s1), Wr.put_bool(on, SpA.w_answer(a, s2)), pre, Equal.cong(String, String, z => Wr.put_bool(on, z), s1, SpA.w_answer(a, s2), at))
      auo.after_checks(s, on, a, s2, pre2, FAu.get_checks(Wr.get_nat(s2)), auo.checks(s2, Wr.get_nat(s2), {==}))
    case Wr.Bad{}:
      Unit{}

def auo.after_on(+s: String, x: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == x : Wr.Dec<Bool>}) -> auo.RP(s, FAu.get_facts.on(x)):
  match x:
    case Wr.Got{+on, +s1}:
      +e = ed
      auo.after_answer(s, on, s1, Wire.wire_bool_exact(s, on, s1, e), FAu.get_answer(Wr.get_nat(s1)), auo.answer(s1, Wr.get_nat(s1), {==}))
    case Wr.Bad{}:
      Unit{}

# a request decoded is spelled
def auo.req(+s: String) -> auo.RP(s, FAu.get_facts(s)):
  auo.after_on(s, Wr.get_bool(s), {==})

def auo.T(s: String) -> Type:
  Sigma<&1, &1, Au.Facts, f => {s == SpA.w_req(f, "") : String}>

# a step answered: a request read whole, nothing left
def auo.top(-s: String, x: Wr.Dec<Au.Facts>, rp: auo.RP(s, x), ok: {LawsBase.wire_opens_err(FAu.ffi.got(x)) == False{} : Bool}) -> auo.T(s):
  match x:
    case Wr.Got{+f, rest}:
      match rest:
        case SNil{}:
          (f, rp)
        case SCon{y, z}:
          LStg.stg.absurd(auo.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(auo.T(s), ok)

def Autonomous.autonomous_entry_reads_only_requests(s, ok):
  auo.top(s, FAu.get_facts(s), auo.req(s), ok)
