# eukhe: the proof of LAW revive_ffi_exact
#
# PROOF: each decoder stage answers a value only for an input that spells
# it before the rest, every number within the wire (wire_nat_exact,
# wire_nat_decoded_fits, wire_bool_exact): rvx.* carries the spelled
# prefix stage by stage; the entry answers no error only for a request
# read whole with nothing left (rvx.top).

import Base
import ../../bend/ffi_revive.bend as FR
import ../../bend/revive.bend as Rv
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/revive.bend as Revive
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../base/staging.bend as LStg

def rvx.and2(a: Bool, -b: Bool, ha: {a == True{} : Bool}, hb: {b == True{} : Bool}) -> {Bool.and(a, b) == True{} : Bool}:
  match a:
    case True{}:
      hb
    case False{}:
      ha

# the facts f spelled before r
def rvx.spell(f: Rv.Facts, r: String) -> String:
  match f:
    case Rv.Facts{fl, a, l, b, n, m, k}:
      Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, Revive.rv_spell_busy(b, Wr.put_nat(n, Wr.put_nat(m, Wr.put_nat(k, r)))))))

def rvx.FP(s: String, d: Wr.Dec<Rv.Facts>) -> Type:
  match d:
    case Wr.Got{f, r}:
      {s == rvx.spell(f, r) : String} & {Revive.rv_fits(f) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# Numbers and flags
# -----------------

def rvx.NP(s: String, d: Wr.Dec<Nat>) -> Type:
  match d:
    case Wr.Got{n, r}:
      {s == Wr.put_nat(n, r) : String} & {LawsBase.wire_fits(n) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rvx.nat.at(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> rvx.NP(s, d):
  match d:
    case Wr.Got{+n, +r}:
      +e2 = ed
      (Wire.wire_nat_exact(s, n, r, e2), Wire.wire_nat_decoded_fits(s, n, r, e2))
    case Wr.Bad{}:
      Unit{}

def rvx.nat(+s: String) -> rvx.NP(s, Wr.get_nat(s)):
  rvx.nat.at(s, Wr.get_nat(s), {==})

def rvx.BP(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def rvx.bool.at(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> rvx.BP(s, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(s, b, r, ed)
    case Wr.Bad{}:
      Unit{}

def rvx.bool(+s: String) -> rvx.BP(s, Wr.get_bool(s)):
  rvx.bool.at(s, Wr.get_bool(s), {==})

# The lease and the busy evidence
# -------------------------------

def rvx.LP(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{l, r}:
      {s == Revive.rv_spell_lease(l, r) : String} & {Revive.rv_lease_fits(l) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rvx.lease.pid(-s: String, -s1: String, pre: {s == Wr.put_nat(1n, s1) : String}, d: Wr.Dec<Nat>, np: rvx.NP(s1, d)) -> rvx.LP(s, FR.get_lease.pid(d)):
  match d:
    case Wr.Got{+p, +r}:
      (e, f) = np
      (Equal.trans(String, s, Wr.put_nat(1n, s1), Wr.put_nat(1n, Wr.put_nat(p, r)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s1, Wr.put_nat(p, r), e)), f)
    case Wr.Bad{}:
      Unit{}

def rvx.lease.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> rvx.LP(s, FR.get_lease.tag(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      rvx.lease.pid(s, s1, pre, Wr.get_nat(s1), rvx.nat(s1))
    case 2n+u:
      Unit{}

def rvx.lease.go(-s: String, d: Wr.Dec<Nat>, np: rvx.NP(s, d)) -> rvx.LP(s, FR.get_lease(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      rvx.lease.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def rvx.lease(+s: String) -> rvx.LP(s, FR.get_lease(Wr.get_nat(s))):
  rvx.lease.go(s, Wr.get_nat(s), rvx.nat(s))

def rvx.BuP(s: String, d: Wr.Dec<Rv.Busy>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Revive.rv_spell_busy(b, r) : String} & {Revive.rv_busy_fits(b) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def rvx.busy.at(-s: String, -s1: String, pre: {s == Wr.put_nat(2n, s1) : String}, d: Wr.Dec<Nat>, np: rvx.NP(s1, d)) -> rvx.BuP(s, FR.get_busy.at(d)):
  match d:
    case Wr.Got{+at, +r}:
      (e, f) = np
      (Equal.trans(String, s, Wr.put_nat(2n, s1), Wr.put_nat(2n, Wr.put_nat(at, r)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s1, Wr.put_nat(at, r), e)), f)
    case Wr.Bad{}:
      Unit{}

def rvx.busy.tag(t: Nat, +s1: String, -s: String, pre: {s == Wr.put_nat(t, s1) : String}) -> rvx.BuP(s, FR.get_busy.tag(t, s1)):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      (pre, {==})
    case 2n:
      rvx.busy.at(s, s1, pre, Wr.get_nat(s1), rvx.nat(s1))
    case 3n+u:
      Unit{}

def rvx.busy.go(-s: String, d: Wr.Dec<Nat>, np: rvx.NP(s, d)) -> rvx.BuP(s, FR.get_busy(d)):
  match d:
    case Wr.Got{t, s1}:
      (e, f) = np
      rvx.busy.tag(t, s1, s, e)
    case Wr.Bad{}:
      Unit{}

def rvx.busy(+s: String) -> rvx.BuP(s, FR.get_busy(Wr.get_nat(s))):
  rvx.busy.go(s, Wr.get_nat(s), rvx.nat(s))

# The facts, stage by stage
# -------------------------

def rvx.skew(-s: String, +fl: Bool, +a: Bool, +l: Maybe<&2, Nat>, +b: Rv.Busy, +n: Nat, +m: Nat, -s7: String, pre: {s == Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, Revive.rv_spell_busy(b, Wr.put_nat(n, Wr.put_nat(m, s7)))))) : String}, fla: {Revive.rv_lease_fits(l) == True{} : Bool}, fb: {Revive.rv_busy_fits(b) == True{} : Bool}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, fm: {LawsBase.wire_fits(m) == True{} : Bool}, d: Wr.Dec<Nat>, np: rvx.NP(s7, d)) -> rvx.FP(s, FR.get_facts.skew(fl, a, l, b, n, m, d)):
  match d:
    case Wr.Got{+k, +r}:
      (e, fk) = np
      (Equal.trans(String, s, Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, Revive.rv_spell_busy(b, Wr.put_nat(n, Wr.put_nat(m, s7)))))), Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, Revive.rv_spell_busy(b, Wr.put_nat(n, Wr.put_nat(m, Wr.put_nat(k, r))))))), pre, Equal.cong(String, String, z => Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, Revive.rv_spell_busy(b, Wr.put_nat(n, Wr.put_nat(m, z)))))), s7, Wr.put_nat(k, r), e)), rvx.and2(Revive.rv_lease_fits(l), Bool.and(Revive.rv_busy_fits(b), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(k)))), fla, rvx.and2(Revive.rv_busy_fits(b), Bool.and(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(k))), fb, rvx.and2(LawsBase.wire_fits(n), Bool.and(LawsBase.wire_fits(m), LawsBase.wire_fits(k)), fn, rvx.and2(LawsBase.wire_fits(m), LawsBase.wire_fits(k), fm, fk)))))
    case Wr.Bad{}:
      Unit{}

def rvx.max(-s: String, +fl: Bool, +a: Bool, +l: Maybe<&2, Nat>, +b: Rv.Busy, +n: Nat, -s6: String, pre: {s == Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, Revive.rv_spell_busy(b, Wr.put_nat(n, s6))))) : String}, fla: {Revive.rv_lease_fits(l) == True{} : Bool}, fb: {Revive.rv_busy_fits(b) == True{} : Bool}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Nat>, np: rvx.NP(s6, d)) -> rvx.FP(s, FR.get_facts.max(fl, a, l, b, n, d)):
  match d:
    case Wr.Got{+m, +r}:
      (e, fm) = np
      rvx.skew(s, fl, a, l, b, n, m, r, Equal.trans(String, s, Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, Revive.rv_spell_busy(b, Wr.put_nat(n, s6))))), Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, Revive.rv_spell_busy(b, Wr.put_nat(n, Wr.put_nat(m, r)))))), pre, Equal.cong(String, String, z => Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, Revive.rv_spell_busy(b, Wr.put_nat(n, z))))), s6, Wr.put_nat(m, r), e)), fla, fb, fn, fm, Wr.get_nat(r), rvx.nat(r))
    case Wr.Bad{}:
      Unit{}

def rvx.now_n(-s: String, +fl: Bool, +a: Bool, +l: Maybe<&2, Nat>, +b: Rv.Busy, -s5: String, pre: {s == Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, Revive.rv_spell_busy(b, s5)))) : String}, fla: {Revive.rv_lease_fits(l) == True{} : Bool}, fb: {Revive.rv_busy_fits(b) == True{} : Bool}, d: Wr.Dec<Nat>, np: rvx.NP(s5, d)) -> rvx.FP(s, FR.get_facts.now.n(fl, a, l, b, d)):
  match d:
    case Wr.Got{+n, +r}:
      (e, fn) = np
      rvx.max(s, fl, a, l, b, n, r, Equal.trans(String, s, Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, Revive.rv_spell_busy(b, s5)))), Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, Revive.rv_spell_busy(b, Wr.put_nat(n, r))))), pre, Equal.cong(String, String, z => Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, Revive.rv_spell_busy(b, z)))), s5, Wr.put_nat(n, r), e)), fla, fb, fn, Wr.get_nat(r), rvx.nat(r))
    case Wr.Bad{}:
      Unit{}

def rvx.now(-s: String, +fl: Bool, +a: Bool, +l: Maybe<&2, Nat>, -s4: String, pre: {s == Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, s4))) : String}, fla: {Revive.rv_lease_fits(l) == True{} : Bool}, d: Wr.Dec<Rv.Busy>, bp: rvx.BuP(s4, d)) -> rvx.FP(s, FR.get_facts.now(fl, a, l, d)):
  match d:
    case Wr.Got{+b, +r}:
      (e, fb) = bp
      rvx.now_n(s, fl, a, l, b, r, Equal.trans(String, s, Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, s4))), Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, Revive.rv_spell_busy(b, r)))), pre, Equal.cong(String, String, z => Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, z))), s4, Revive.rv_spell_busy(b, r), e)), fla, fb, Wr.get_nat(r), rvx.nat(r))
    case Wr.Bad{}:
      Unit{}

def rvx.facts_busy(-s: String, +fl: Bool, +a: Bool, -s3: String, pre: {s == Wr.put_bool(fl, Wr.put_bool(a, s3)) : String}, d: Wr.Dec<Maybe<&2, Nat>>, lp: rvx.LP(s3, d)) -> rvx.FP(s, FR.get_facts.busy(fl, a, d)):
  match d:
    case Wr.Got{+l, +r}:
      (e, fla) = lp
      rvx.now(s, fl, a, l, r, Equal.trans(String, s, Wr.put_bool(fl, Wr.put_bool(a, s3)), Wr.put_bool(fl, Wr.put_bool(a, Revive.rv_spell_lease(l, r))), pre, Equal.cong(String, String, z => Wr.put_bool(fl, Wr.put_bool(a, z)), s3, Revive.rv_spell_lease(l, r), e)), fla, FR.get_busy(Wr.get_nat(r)), rvx.busy(r))
    case Wr.Bad{}:
      Unit{}

def rvx.facts_lease(-s: String, +fl: Bool, -s2: String, pre: {s == Wr.put_bool(fl, s2) : String}, d: Wr.Dec<Bool>, bp: rvx.BP(s2, d)) -> rvx.FP(s, FR.get_facts.lease(fl, d)):
  match d:
    case Wr.Got{+a, +r}:
      rvx.facts_busy(s, fl, a, r, Equal.trans(String, s, Wr.put_bool(fl, s2), Wr.put_bool(fl, Wr.put_bool(a, r)), pre, Equal.cong(String, String, z => Wr.put_bool(fl, z), s2, Wr.put_bool(a, r), bp)), FR.get_lease(Wr.get_nat(r)), rvx.lease(r))
    case Wr.Bad{}:
      Unit{}

def rvx.facts(-s: String, d: Wr.Dec<Bool>, bp: rvx.BP(s, d)) -> rvx.FP(s, FR.get_facts.archived(d)):
  match d:
    case Wr.Got{+fl, +r}:
      rvx.facts_lease(s, fl, r, bp, Wr.get_bool(r), rvx.bool(r))
    case Wr.Bad{}:
      Unit{}

# The entry
# ---------

def rvx.G(s: String) -> Type:
  Sigma<&1, &1, Rv.Facts, f => {s == Revive.rv_spell(f) : String} & {Revive.rv_fits(f) == True{} : Bool}>

def rvx.whole(-s: String, f: Rv.Facts, fp: rvx.FP(s, Wr.Got{f, ""})) -> rvx.G(s):
  match f:
    case Rv.Facts{fl, a, l, b, n, m, k}:
      (Rv.Facts{fl, a, l, b, n, m, k}, fp)

def rvx.top(-s: String, d: Wr.Dec<Rv.Facts>, fp: rvx.FP(s, d), ok: {LawsBase.wire_opens_err(FR.ffi.go(d)) == False{} : Bool}) -> rvx.G(s):
  match d:
    case Wr.Got{+f, rest}:
      match rest:
        case SNil{}:
          rvx.whole(s, f, fp)
        case SCon{x, y}:
          LStg.stg.absurd(rvx.G(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(rvx.G(s), ok)

def Revive.revive_ffi_exact(s, ok):
  rvx.top(s, FR.get_facts(s), rvx.facts(s, Wr.get_bool(s), rvx.bool(s)), ok)
