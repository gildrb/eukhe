# eukhe: the proof of LAW runners_ffi_reads_only_requests
#
# PROOF: each decoder stage answers a value only for an input that spells it before the rest (wire_nat_exact, wire_bool_exact; rro.* carry the spelled prefix stage by stage); the entry answers no error only for a request read whole with nothing left (rro.top).

import Base
import ../../bend/ffi_runners.bend as FRu
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/runners.bend as Runners
import ../base/staging.bend as LStg
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_bool_exact.bend as PWireBoolExact

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

def rro.QP(s: String, d: Wr.Dec<FRu.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Runners.spell_req(q, r) : String}
    case Wr.Bad{}:
      Unit

def rro.main(-s: String, -s1: String, pre: {s == Wr.put_nat(3n, s1) : String}, d: Wr.Dec<Bool>, bp: rro.BP(s1, d)) -> rro.QP(s, FRu.get_main(d)):
  match d:
    case Wr.Got{+h, +r}:
      Equal.trans(String, s, Wr.put_nat(3n, s1), Wr.put_nat(3n, Wr.put_bool(h, r)), pre, Equal.cong(String, String, z => Wr.put_nat(3n, z), s1, Wr.put_bool(h, r), bp))
    case Wr.Bad{}:
      Unit{}

def rro.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> rro.QP(s, FRu.get_req.tag(t, s1)):
  match t:
    case 0n:
      Unit{}
    case 1n:
      Unit{}
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
