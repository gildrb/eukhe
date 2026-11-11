# eukhe: the proof of LAW prior_entry_reads_only_requests
#
# PROOF: each stage of the request's decoder answers Got only for the
# spelling of what it read before the rest (wire_nat_exact,
# wire_bool_exact), its numbers within the wire (wire_nat_decoded_fits):
# pro.req. An answer that is no error comes from a request read whole,
# nothing left (pro.main, pro.fin).

import Base
import ../../bend/ffi_work.bend as FW
import ../../bend/progress.bend as Pr
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../../laws/work.bend as Work
import ../wire/base/spell.bend as LAWireSpell

# the request of the last check m, then rest
def pro.spell(m: Maybe<&2, Pr.Last>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      match x:
        case Pr.Last{r, g, s, w}:
          Wr.put_nat(1n, Wr.put_bool(r, Wr.put_bool(g, Wr.put_nat(s, Wr.put_nat(w, rest)))))

def pro.spell_req(m: Maybe<&2, Pr.Last>) -> {pro.spell(m, "") == Work.pe_spell_req(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      match x:
        case Pr.Last{r, g, s, w}:
          {==}

# what a decoded request says about the input s
def pro.P(s: String, d: Wr.Dec<Maybe<&2, Pr.Last>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == pro.spell(m, r) : String} & {Work.pe_fits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def pro.work(-s: String, +r: Bool, +g: Bool, +n: Nat, +s4: String, pre: {s == Wr.put_nat(1n, Wr.put_bool(r, Wr.put_bool(g, Wr.put_nat(n, s4)))) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s4) == d : Wr.Dec<Nat>}) -> pro.P(s, FW.get_last.work(r, g, n, d)):
  match d:
    case Wr.Got{+w, +s5}:
      +e = ed
      (Equal.trans(String, s, Wr.put_nat(1n, Wr.put_bool(r, Wr.put_bool(g, Wr.put_nat(n, s4)))), Wr.put_nat(1n, Wr.put_bool(r, Wr.put_bool(g, Wr.put_nat(n, Wr.put_nat(w, s5))))), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_bool(r, Wr.put_bool(g, Wr.put_nat(n, z)))), s4, Wr.put_nat(w, s5), Wire.wire_nat_exact(s4, w, s5, e))),
        LAWireSpell.ws_and_tt(LawsBase.wire_fits(n), LawsBase.wire_fits(w), fn, Wire.wire_nat_decoded_fits(s4, w, s5, e)))
    case Wr.Bad{}:
      Unit{}

def pro.stalls(-s: String, +r: Bool, +g: Bool, +s3: String, pre: {s == Wr.put_nat(1n, Wr.put_bool(r, Wr.put_bool(g, s3))) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> pro.P(s, FW.get_last.stalls(r, g, d)):
  match d:
    case Wr.Got{+n, +s4}:
      +e = ed
      pro.work(s, r, g, n, s4,
        Equal.trans(String, s, Wr.put_nat(1n, Wr.put_bool(r, Wr.put_bool(g, s3))), Wr.put_nat(1n, Wr.put_bool(r, Wr.put_bool(g, Wr.put_nat(n, s4)))), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_bool(r, Wr.put_bool(g, z))), s3, Wr.put_nat(n, s4), Wire.wire_nat_exact(s3, n, s4, e))),
        Wire.wire_nat_decoded_fits(s3, n, s4, e), Wr.get_nat(s4), {==})
    case Wr.Bad{}:
      Unit{}

def pro.goal(-s: String, +r: Bool, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_bool(r, s2)) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> pro.P(s, FW.get_last.goal(r, d)):
  match d:
    case Wr.Got{+g, +s3}:
      pro.stalls(s, r, g, s3,
        Equal.trans(String, s, Wr.put_nat(1n, Wr.put_bool(r, s2)), Wr.put_nat(1n, Wr.put_bool(r, Wr.put_bool(g, s3))), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, Wr.put_bool(r, z)), s2, Wr.put_bool(g, s3), Wire.wire_bool_exact(s2, g, s3, ed))),
        Wr.get_nat(s3), {==})
    case Wr.Bad{}:
      Unit{}

def pro.run(-s: String, +s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> pro.P(s, FW.get_last.run(d)):
  match d:
    case Wr.Got{+r, +s2}:
      pro.goal(s, r, s2,
        Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_bool(r, s2)), pre,
          Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_bool(r, s2), Wire.wire_bool_exact(s1, r, s2, ed))),
        Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

def pro.tag(-s: String, n: Nat, +s1: String, pre: {s == Wr.put_nat(n, s1) : String}) -> pro.P(s, FW.get_last.tag(n, s1)):
  match n:
    case 0n:
      (pre, {==})
    case 1n:
      pro.run(s, s1, pre, Wr.get_bool(s1), {==})
    case 2n+q:
      Unit{}

def pro.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> pro.P(s, FW.get_last.go(d)):
  match d:
    case Wr.Got{+n, +s1}:
      pro.tag(s, n, s1, Wire.wire_nat_exact(s, n, s1, ed))
    case Wr.Bad{}:
      Unit{}

# a decoded request is spelled, and its numbers fit
def pro.req(+s: String) -> pro.P(s, FW.get_last(s)):
  pro.go(s, Wr.get_nat(s), {==})

def pro.G(s: String) -> Type:
  &m: Maybe<&2, Pr.Last> -> {(s, Work.pe_fits(m)) == (Work.pe_spell_req(m), True{}) : String & Bool}

def pro.top(-s: String, +m: Maybe<&2, Pr.Last>, e: {s == Work.pe_spell_req(m) : String}, f: {Work.pe_fits(m) == True{} : Bool}) -> {(s, Work.pe_fits(m)) == (Work.pe_spell_req(m), True{}) : String & Bool}:
  %e : {(s, Work.pe_fits(m)) == (_, True{}) : String & Bool}
  %f : {(s, Work.pe_fits(m)) == (s, _) : String & Bool}
  {==}

def pro.fin(+s: String, +m: Maybe<&2, Pr.Last>, r: String, pre: {s == pro.spell(m, r) : String}, f: {Work.pe_fits(m) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FW.run.end(Wr.end(r), m)) == False{} : Bool}) -> pro.G(s):
  match r:
    case SNil{}:
      (m, pro.top(s, m, Equal.trans(String, s, pro.spell(m, ""), Work.pe_spell_req(m), pre, pro.spell_req(m)), f))
    case SCon{c, t}:
      LAWireSpell.ws_absurd(pro.G(s), ok)

def pro.main(+s: String, d: Wr.Dec<Maybe<&2, Pr.Last>>, inv: pro.P(s, d), ok: {LawsBase.wire_opens_err(FW.run(d)) == False{} : Bool}) -> pro.G(s):
  match d:
    case Wr.Got{+m, +r}:
      (e, f) = inv
      pro.fin(s, m, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(pro.G(s), ok)

def Work.prior_entry_reads_only_requests(s, ok):
  pro.main(s, FW.get_last(s), pro.req(s), ok)
