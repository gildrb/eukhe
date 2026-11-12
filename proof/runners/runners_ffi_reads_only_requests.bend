# eukhe: the proof of LAW runners_ffi_reads_only_requests
#
# PROOF: each decoder stage answers a value only for an input that spells it before the rest (wire_nat_exact, wire_bool_exact, wire_list_exact; rro.* carry the spelled prefix stage by stage); the entry answers no error only for a request read whole with nothing left (rro.top).

import Base
import ../../bend/runners.bend as Ru
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/runners.bend as Runners
import ../base/staging.bend as LStg
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/wire_list_exact.bend as PWireListExact

def rro.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String}
    case Wr.Bad{}:
      Unit

def rro.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> rro.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      Wire.wire_nat_exact(s, n, r, ed)
    case Wr.Bad{}:
      Unit{}

def rro.nat(+s: String) -> rro.NP(s, Wr.get_nat(s)):
  rro.nat.at(s, Wr.get_nat(s), {==})

def rro.BP(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def rro.bool.at(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> rro.BP(s, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(s, b, r, ed)
    case Wr.Bad{}:
      Unit{}

def rro.bool(+s: String) -> rro.BP(s, Wr.get_bool(s)):
  rro.bool.at(s, Wr.get_bool(s), {==})

def rro.LP(s: String, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Runners.spell_ns(xs, r) : String}
    case Wr.Bad{}:
      Unit

def rro.ns.at(+s: String, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s) == d : Wr.Dec<List<&2, Nat>>}) -> rro.LP(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      Wire.wire_list_exact(s, xs, r, ed)
    case Wr.Bad{}:
      Unit{}

def rro.ns(+s: String) -> rro.LP(s, FRu.get_ns(s)):
  rro.ns.at(s, Wr.get_list(~Nat, ~Wr.get_nat, s), {==})

def rro.KP(s: String, d: Wr.Dec<Ru.Asker>) -> Type:
  match d:
    case Wr.Got{k, r}:
      {s == Runners.spell_asker(k, r) : String}
    case Wr.Bad{}:
      Unit

def rro.says(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Bool>, bp: rro.BP(s1, d)) -> rro.KP(s, FRu.get_says(d)):
  match d:
    case Wr.Got{+y, +r}:
      Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_bool(y, r)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_bool(y, r), bp))
    case Wr.Bad{}:
      Unit{}

def rro.asker.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> rro.KP(s, FRu.get_asker.tag(t, s1)):
  match t:
    case 0n:
      pre
    case 1n:
      pre
    case 2n:
      rro.says(s, s1, pre, Wr.get_bool(s1), rro.bool(s1))
    case 3n+u:
      Unit{}

def rro.asker(-s: String, d: Wr.Dec<Nat>, np: rro.NP(s, d)) -> rro.KP(s, FRu.get_asker(d)):
  match d:
    case Wr.Got{t, +s1}:
      rro.asker.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def rro.QP(s: String, d: Wr.Dec<FRu.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Runners.spell_req(q, r) : String}
    case Wr.Bad{}:
      Unit

# within: the caps, then the auto set
def rro.within.auto(-s: String, +c: List<&2, Nat>, -s2: String, pre: {s == Wr.put_nat(0n, Runners.spell_ns(c, s2)) : String}, d: Wr.Dec<List<&2, Nat>>, lp: rro.LP(s2, d)) -> rro.QP(s, FRu.get_within.auto(c, d)):
  match d:
    case Wr.Got{+a, +r}:
      Equal.trans(String, s, Wr.put_nat(0n, Runners.spell_ns(c, s2)), Wr.put_nat(0n, Runners.spell_ns(c, Runners.spell_ns(a, r))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, Runners.spell_ns(c, z)), s2, Runners.spell_ns(a, r), lp))
    case Wr.Bad{}:
      Unit{}

def rro.within(-s: String, -s1: String, pre: {s == Wr.put_nat(0n, s1) : String}, d: Wr.Dec<List<&2, Nat>>, lp: rro.LP(s1, d)) -> rro.QP(s, FRu.get_within(d)):
  match d:
    case Wr.Got{+c, +r}:
      rro.within.auto(s, c, r, Equal.trans(String, s, Wr.put_nat(0n, s1), Wr.put_nat(0n, Runners.spell_ns(c, r)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s1, Runners.spell_ns(c, r), lp)), FRu.get_ns(r), rro.ns(r))
    case Wr.Bad{}:
      Unit{}

# cell: the caps, the auto set, then the asker
def rro.cell.asker(-s: String, +c: List<&2, Nat>, +a: List<&2, Nat>, -s3: String, pre: {s == Wr.put_nat(1n, Runners.spell_ns(c, Runners.spell_ns(a, s3))) : String}, d: Wr.Dec<Ru.Asker>, kp: rro.KP(s3, d)) -> rro.QP(s, FRu.get_cell.asker(c, a, d)):
  match d:
    case Wr.Got{+k, +r}:
      Equal.trans(String, s, Wr.put_nat(1n, Runners.spell_ns(c, Runners.spell_ns(a, s3))), Wr.put_nat(1n, Runners.spell_ns(c, Runners.spell_ns(a, Runners.spell_asker(k, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Runners.spell_ns(c, Runners.spell_ns(a, z))), s3, Runners.spell_asker(k, r), kp))
    case Wr.Bad{}:
      Unit{}

def rro.cell.auto(-s: String, +c: List<&2, Nat>, -s2: String, pre: {s == Wr.put_nat(1n, Runners.spell_ns(c, s2)) : String}, d: Wr.Dec<List<&2, Nat>>, lp: rro.LP(s2, d)) -> rro.QP(s, FRu.get_cell.auto(c, d)):
  match d:
    case Wr.Got{+a, +r}:
      rro.cell.asker(s, c, a, r, Equal.trans(String, s, Wr.put_nat(1n, Runners.spell_ns(c, s2)), Wr.put_nat(1n, Runners.spell_ns(c, Runners.spell_ns(a, r))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, Runners.spell_ns(c, z)), s2, Runners.spell_ns(a, r), lp)), FRu.get_asker(Wr.get_nat(r)), rro.asker(r, Wr.get_nat(r), rro.nat(r)))
    case Wr.Bad{}:
      Unit{}

def rro.cell(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<List<&2, Nat>>, lp: rro.LP(s1, d)) -> rro.QP(s, FRu.get_cell(d)):
  match d:
    case Wr.Got{+c, +r}:
      rro.cell.auto(s, c, r, Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Runners.spell_ns(c, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Runners.spell_ns(c, r), lp)), FRu.get_ns(r), rro.ns(r))
    case Wr.Bad{}:
      Unit{}

def rro.main(-s: String, -s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Bool>, bp: rro.BP(s1, d)) -> rro.QP(s, FRu.get_main(d)):
  match d:
    case Wr.Got{+h, +r}:
      Equal.trans(String, s, Wr.put_nat(3n, s1), Wr.put_nat(3n, Wr.put_bool(h, r)), pre, Equal.cong(String, String, z => Wr.put_nat(3n, z), s1, Wr.put_bool(h, r), bp))
    case Wr.Bad{}:
      Unit{}

def rro.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> rro.QP(s, FRu.get_req.tag(t, s1)):
  match t:
    case 0n:
      rro.within(s, s1, pre, FRu.get_ns(s1), rro.ns(s1))
    case 1n:
      rro.cell(s, s1, pre, FRu.get_ns(s1), rro.ns(s1))
    case 2n:
      pre
    case 3n:
      rro.main(s, s1, pre, Wr.get_bool(s1), rro.bool(s1))
    case 4n+u:
      Unit{}

def rro.go(-s: String, d: Wr.Dec<Nat>, np: rro.NP(s, d)) -> rro.QP(s, FRu.get_req.go(d)):
  match d:
    case Wr.Got{t, +s1}:
      rro.tag(t, s1, s, np)
    case Wr.Bad{}:
      Unit{}

def rro.G(s: String) -> Type:
  Sigma<&1, &1, FRu.Req, q => {s == Runners.spell_req(q, "") : String}>

def rro.top(-s: String, d: Wr.Dec<FRu.Req>, qp: rro.QP(s, d), ok: {LawsBase.wire_opens_err(FRu.run(d)) == False{} : Bool}) -> rro.G(s):
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, qp)
        case SCon{x, y}:
          LStg.stg.absurd(rro.G(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(rro.G(s), ok)

def Runners.runners_ffi_reads_only_requests(s, ok):
  rro.top(s, FRu.get_req(s), rro.go(s, Wr.get_nat(s), rro.nat(s)), ok)
