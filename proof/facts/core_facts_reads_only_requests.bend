# eukhe: the proof of LAW core_facts_reads_only_requests
#
# PROOF: whatever a decoder of the entry reads is the grammar's spelling of
# what it read, then its rest, and fits the wire (fd.*, field by field with
# the wire's exactness laws: an unknown tag is Bad); the stages carry the
# input spelled up to their field (`pre`), so an answer that is no error
# comes from a request read whole, nothing left, and is the spelled reply
# of the model's decision (fro.fin with LA.fs.answer).

import Base
import ../../bend/facts.bend as Fx
import ../../bend/ffi_facts.bend as FFx
import ../../bend/wire.bend as Wr
import ../../laws/facts/budgets.bend as FactsBudgets
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../wire/wire_bool_exact.bend as PWireBoolExact
import ../wire/base/spell.bend as LAWireSpell
import ./base.bend as LA

# s spelled up to a field a is s spelled up to its spelling b
def fd.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# Decoders: what each reads is its spelling, then its rest, and fits
# ------------------------------------------------------------------

def fd.MN(s: String, d: Wr.Dec<Maybe<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == FactsBudgets.facts_spell_mnat(x, r) : String} & {LawsBase.core_mfits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def fd.EL(s: String, d: Wr.Dec<Fx.ELv>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == FactsBudgets.facts_spell_elv(x, r) : String}
    case Wr.Bad{}:
      Unit

def fd.LV(s: String, d: Wr.Dec<Fx.Lv>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == FactsBudgets.facts_spell_lv(x, r) : String}
    case Wr.Bad{}:
      Unit

def fd.CU(s: String, d: Wr.Dec<Fx.Customs>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == FactsBudgets.facts_spell_customs(x, r) : String} & {FactsBudgets.core_customs_fit(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def fd.BU(s: String, d: Wr.Dec<Fx.Budgets>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == FactsBudgets.facts_spell_budgets(x, r) : String} & {FactsBudgets.core_budgets_fit(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def fd.MB(s: String, d: Wr.Dec<Maybe<&2, Fx.Budgets>>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == FactsBudgets.facts_spell_mbudgets(x, r) : String} & {FactsBudgets.core_mbudgets_fit(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def fd.Req(s: String, d: Wr.Dec<FFx.Req>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == FactsBudgets.facts_spell_req(x, r) : String} & {FactsBudgets.core_facts_req_fits(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a presence tag: 0 none, 1 then a Nat that fits
def fd.mnat.some(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> fd.MN(s, FFx.get_mnat.some(d)):
  match d:
    case Wr.Got{+x, +s1}:
      +ee = ed
      (fd.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(x, s1), pre, Wire.wire_nat_exact(s0, x, s1, ee)), Wire.wire_nat_decoded_fits(s0, x, s1, ee))
    case Wr.Bad{}:
      Unit{}

def fd.mnat.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> fd.MN(s, FFx.get_mnat.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s0, ed), {==})
        case 1n:
          fd.mnat.some(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def fd.mnat(+s: String) -> fd.MN(s, FFx.get_mnat(s)):
  fd.mnat.go(s, Wr.get_nat(s), {==})

# a request's level: tags 0 to 5
def fd.elv.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> fd.EL(s, FFx.get_elv.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s0, ed)
        case 3n:
          Wire.wire_nat_exact(s, 3n, s0, ed)
        case 4n:
          Wire.wire_nat_exact(s, 4n, s0, ed)
        case 5n:
          Wire.wire_nat_exact(s, 5n, s0, ed)
        case 6n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def fd.elv(+s: String) -> fd.EL(s, FFx.get_elv(s)):
  fd.elv.go(s, Wr.get_nat(s), {==})

# a budget level: tags 0 to 3
def fd.lv.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> fd.LV(s, FFx.get_lv.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          Wire.wire_nat_exact(s, 0n, s0, ed)
        case 1n:
          Wire.wire_nat_exact(s, 1n, s0, ed)
        case 2n:
          Wire.wire_nat_exact(s, 2n, s0, ed)
        case 3n:
          Wire.wire_nat_exact(s, 3n, s0, ed)
        case 4n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def fd.lv(+s: String) -> fd.LV(s, FFx.get_lv(s)):
  fd.lv.go(s, Wr.get_nat(s), {==})

# the user's budgets: four presence tags
def fd.cus.s3(+s: String, +v0: Maybe<&2, Nat>, +v1: Maybe<&2, Nat>, +v2: Maybe<&2, Nat>, +s3: String, pre: {s == FactsBudgets.facts_spell_mnat(v0, FactsBudgets.facts_spell_mnat(v1, FactsBudgets.facts_spell_mnat(v2, s3))) : String}, f0: {LawsBase.core_mfits(v0) == True{} : Bool}, f1: {LawsBase.core_mfits(v1) == True{} : Bool}, f2: {LawsBase.core_mfits(v2) == True{} : Bool}, d: Wr.Dec<Maybe<&2, Nat>>, xd: fd.MN(s3, d)) -> fd.CU(s, FFx.get_customs.of(FFx.seq.fin(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, FFx.P2{FFx.P2{v0, v1}, v2}, d))):
  match d:
    case Wr.Got{+v3, +r}:
      (e, fj) = xd
      +f3 = fj
      (fd.step(z => FactsBudgets.facts_spell_mnat(v0, FactsBudgets.facts_spell_mnat(v1, FactsBudgets.facts_spell_mnat(v2, z))), s, s3, FactsBudgets.facts_spell_mnat(v3, r), pre, e), LAWireSpell.ws_and_tt(LawsBase.core_mfits(v0), Bool.and(LawsBase.core_mfits(v1), Bool.and(LawsBase.core_mfits(v2), LawsBase.core_mfits(v3))), f0, LAWireSpell.ws_and_tt(LawsBase.core_mfits(v1), Bool.and(LawsBase.core_mfits(v2), LawsBase.core_mfits(v3)), f1, LAWireSpell.ws_and_tt(LawsBase.core_mfits(v2), LawsBase.core_mfits(v3), f2, f3))))
    case Wr.Bad{}:
      Unit{}

def fd.cus.s2(+s: String, +v0: Maybe<&2, Nat>, +v1: Maybe<&2, Nat>, +s2: String, pre: {s == FactsBudgets.facts_spell_mnat(v0, FactsBudgets.facts_spell_mnat(v1, s2)) : String}, f0: {LawsBase.core_mfits(v0) == True{} : Bool}, f1: {LawsBase.core_mfits(v1) == True{} : Bool}, d: Wr.Dec<Maybe<&2, Nat>>, xd: fd.MN(s2, d)) -> fd.CU(s, FFx.get_customs.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq.fin(~FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, FFx.P2{v0, v1}, d)))):
  match d:
    case Wr.Got{+v2, +r}:
      (e, fj) = xd
      fd.cus.s3(s, v0, v1, v2, r, fd.step(z => FactsBudgets.facts_spell_mnat(v0, FactsBudgets.facts_spell_mnat(v1, z)), s, s2, FactsBudgets.facts_spell_mnat(v2, r), pre, e), f0, f1, fj, FFx.get_mnat(r), fd.mnat(r))
    case Wr.Bad{}:
      Unit{}

def fd.cus.s1(+s: String, +v0: Maybe<&2, Nat>, +s1: String, pre: {s == FactsBudgets.facts_spell_mnat(v0, s1) : String}, f0: {LawsBase.core_mfits(v0) == True{} : Bool}, d: Wr.Dec<Maybe<&2, Nat>>, xd: fd.MN(s1, d)) -> fd.CU(s, FFx.get_customs.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq.fin(~Maybe<&2, Nat>, ~Maybe<&2, Nat>, v0, d))))):
  match d:
    case Wr.Got{+v1, +r}:
      (e, fj) = xd
      fd.cus.s2(s, v0, v1, r, fd.step(z => FactsBudgets.facts_spell_mnat(v0, z), s, s1, FactsBudgets.facts_spell_mnat(v1, r), pre, e), f0, fj, FFx.get_mnat(r), fd.mnat(r))
    case Wr.Bad{}:
      Unit{}

def fd.cus.s0(+s: String, d: Wr.Dec<Maybe<&2, Nat>>, xd: fd.MN(s, d)) -> fd.CU(s, FFx.get_customs.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Maybe<&2, Nat>>, ~Maybe<&2, Nat>, ~FFx.get_mnat, FFx.seq(~Maybe<&2, Nat>, ~Maybe<&2, Nat>, ~FFx.get_mnat, d))))):
  match d:
    case Wr.Got{+v0, +r}:
      (e, fj) = xd
      fd.cus.s1(s, v0, r, e, fj, FFx.get_mnat(r), fd.mnat(r))
    case Wr.Bad{}:
      Unit{}

def fd.cus(+s: String) -> fd.CU(s, FFx.get_customs(s)):
  fd.cus.s0(s, FFx.get_mnat(s), fd.mnat(s))

# a budget table: four Nats
def fd.bud.s3(+s: String, +v0: Nat, +v1: Nat, +v2: Nat, +s3: String, pre: {s == Wr.put_nat(v0, Wr.put_nat(v1, Wr.put_nat(v2, s3))) : String}, f0: {LawsBase.wire_fits(v0) == True{} : Bool}, f1: {LawsBase.wire_fits(v1) == True{} : Bool}, f2: {LawsBase.wire_fits(v2) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> fd.BU(s, FFx.get_budgets.of(FFx.seq.fin(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, FFx.P2{FFx.P2{v0, v1}, v2}, d))):
  match d:
    case Wr.Got{+v3, +r}:
      +ee = ed
      +f3 = Wire.wire_nat_decoded_fits(s3, v3, r, ee)
      (fd.step(z => Wr.put_nat(v0, Wr.put_nat(v1, Wr.put_nat(v2, z))), s, s3, Wr.put_nat(v3, r), pre, Wire.wire_nat_exact(s3, v3, r, ee)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(v0), Bool.and(LawsBase.wire_fits(v1), Bool.and(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3))), f0, LAWireSpell.ws_and_tt(LawsBase.wire_fits(v1), Bool.and(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3)), f1, LAWireSpell.ws_and_tt(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3), f2, f3))))
    case Wr.Bad{}:
      Unit{}

def fd.bud.s2(+s: String, +v0: Nat, +v1: Nat, +s2: String, pre: {s == Wr.put_nat(v0, Wr.put_nat(v1, s2)) : String}, f0: {LawsBase.wire_fits(v0) == True{} : Bool}, f1: {LawsBase.wire_fits(v1) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> fd.BU(s, FFx.get_budgets.of(FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~FFx.P2<Nat, Nat>, ~Nat, FFx.P2{v0, v1}, d)))):
  match d:
    case Wr.Got{+v2, +r}:
      +ee = ed
      fd.bud.s3(s, v0, v1, v2, r, fd.step(z => Wr.put_nat(v0, Wr.put_nat(v1, z)), s, s2, Wr.put_nat(v2, r), pre, Wire.wire_nat_exact(s2, v2, r, ee)), f0, f1, Wire.wire_nat_decoded_fits(s2, v2, r, ee), Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def fd.bud.s1(+s: String, +v0: Nat, +s1: String, pre: {s == Wr.put_nat(v0, s1) : String}, f0: {LawsBase.wire_fits(v0) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> fd.BU(s, FFx.get_budgets.of(FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~Nat, ~Nat, v0, d))))):
  match d:
    case Wr.Got{+v1, +r}:
      +ee = ed
      fd.bud.s2(s, v0, v1, r, fd.step(z => Wr.put_nat(v0, z), s, s1, Wr.put_nat(v1, r), pre, Wire.wire_nat_exact(s1, v1, r, ee)), f0, Wire.wire_nat_decoded_fits(s1, v1, r, ee), Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def fd.bud.s0(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> fd.BU(s, FFx.get_budgets.of(FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~Nat, ~Nat, ~Wr.get_nat, d))))):
  match d:
    case Wr.Got{+v0, +r}:
      +ee = ed
      fd.bud.s1(s, v0, r, Wire.wire_nat_exact(s, v0, r, ee), Wire.wire_nat_decoded_fits(s, v0, r, ee), Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def fd.bud(+s: String) -> fd.BU(s, FFx.get_budgets(s)):
  fd.bud.s0(s, Wr.get_nat(s), {==})

# a budget rule: 0 none, 1 then a table
def fd.mb.some(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Fx.Budgets>, xd: fd.BU(s0, d)) -> fd.MB(s, FFx.get_mbudgets.some(d)):
  match d:
    case Wr.Got{+b, +s1}:
      (e, fb) = xd
      (fd.step(z => Wr.put_nat(1n, z), s, s0, FactsBudgets.facts_spell_budgets(b, s1), pre, e), fb)
    case Wr.Bad{}:
      Unit{}

def fd.mb.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> fd.MB(s, FFx.get_mbudgets.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          (Wire.wire_nat_exact(s, 0n, s0, ed), {==})
        case 1n:
          fd.mb.some(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), FFx.get_budgets(s0), fd.bud(s0))
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

def fd.mb(+s: String) -> fd.MB(s, FFx.get_mbudgets(s)):
  fd.mb.go(s, Wr.get_nat(s), {==})

# the window facts: four Nats, then a Bool
def fd.WI(s: String, d: Wr.Dec<Fx.Win>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == FactsBudgets.facts_spell_win(x, r) : String} & {FactsBudgets.core_win_fit(x) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def fd.win.s4(+s: String, +v0: Nat, +v1: Nat, +v2: Nat, +v3: Nat, +s4: String, pre: {s == Wr.put_nat(v0, Wr.put_nat(v1, Wr.put_nat(v2, Wr.put_nat(v3, s4)))) : String}, f0: {LawsBase.wire_fits(v0) == True{} : Bool}, f1: {LawsBase.wire_fits(v1) == True{} : Bool}, f2: {LawsBase.wire_fits(v2) == True{} : Bool}, f3: {LawsBase.wire_fits(v3) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s4) == d : Wr.Dec<Bool>}) -> fd.WI(s, FFx.get_win.of(FFx.seq.fin(~FFx.P2<FFx.P2<FFx.P2<Nat, Nat>, Nat>, Nat>, ~Bool, FFx.P2{FFx.P2{FFx.P2{v0, v1}, v2}, v3}, d))):
  match d:
    case Wr.Got{+v4, +r}:
      +ee = ed
      (fd.step(z => Wr.put_nat(v0, Wr.put_nat(v1, Wr.put_nat(v2, Wr.put_nat(v3, z)))), s, s4, Wr.put_bool(v4, r), pre, Wire.wire_bool_exact(s4, v4, r, ee)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(v0), Bool.and(LawsBase.wire_fits(v1), Bool.and(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3))), f0, LAWireSpell.ws_and_tt(LawsBase.wire_fits(v1), Bool.and(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3)), f1, LAWireSpell.ws_and_tt(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3), f2, f3))))
    case Wr.Bad{}:
      Unit{}

def fd.win.s3(+s: String, +v0: Nat, +v1: Nat, +v2: Nat, +s3: String, pre: {s == Wr.put_nat(v0, Wr.put_nat(v1, Wr.put_nat(v2, s3))) : String}, f0: {LawsBase.wire_fits(v0) == True{} : Bool}, f1: {LawsBase.wire_fits(v1) == True{} : Bool}, f2: {LawsBase.wire_fits(v2) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> fd.WI(s, FFx.get_win.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Nat, Nat>, Nat>, Nat>, ~Bool, ~Wr.get_bool, FFx.seq.fin(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, FFx.P2{FFx.P2{v0, v1}, v2}, d)))):
  match d:
    case Wr.Got{+v3, +r}:
      +ee = ed
      fd.win.s4(s, v0, v1, v2, v3, r, fd.step(z => Wr.put_nat(v0, Wr.put_nat(v1, Wr.put_nat(v2, z))), s, s3, Wr.put_nat(v3, r), pre, Wire.wire_nat_exact(s3, v3, r, ee)), f0, f1, f2, Wire.wire_nat_decoded_fits(s3, v3, r, ee), Wr.get_bool(r), {==})
    case Wr.Bad{}:
      Unit{}

def fd.win.s2(+s: String, +v0: Nat, +v1: Nat, +s2: String, pre: {s == Wr.put_nat(v0, Wr.put_nat(v1, s2)) : String}, f0: {LawsBase.wire_fits(v0) == True{} : Bool}, f1: {LawsBase.wire_fits(v1) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> fd.WI(s, FFx.get_win.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Nat, Nat>, Nat>, Nat>, ~Bool, ~Wr.get_bool, FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~FFx.P2<Nat, Nat>, ~Nat, FFx.P2{v0, v1}, d))))):
  match d:
    case Wr.Got{+v2, +r}:
      +ee = ed
      fd.win.s3(s, v0, v1, v2, r, fd.step(z => Wr.put_nat(v0, Wr.put_nat(v1, z)), s, s2, Wr.put_nat(v2, r), pre, Wire.wire_nat_exact(s2, v2, r, ee)), f0, f1, Wire.wire_nat_decoded_fits(s2, v2, r, ee), Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def fd.win.s1(+s: String, +v0: Nat, +s1: String, pre: {s == Wr.put_nat(v0, s1) : String}, f0: {LawsBase.wire_fits(v0) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> fd.WI(s, FFx.get_win.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Nat, Nat>, Nat>, Nat>, ~Bool, ~Wr.get_bool, FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~Nat, ~Nat, v0, d)))))):
  match d:
    case Wr.Got{+v1, +r}:
      +ee = ed
      fd.win.s2(s, v0, v1, r, fd.step(z => Wr.put_nat(v0, z), s, s1, Wr.put_nat(v1, r), pre, Wire.wire_nat_exact(s1, v1, r, ee)), f0, Wire.wire_nat_decoded_fits(s1, v1, r, ee), Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def fd.win.s0(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> fd.WI(s, FFx.get_win.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Nat, Nat>, Nat>, Nat>, ~Bool, ~Wr.get_bool, FFx.seq(~FFx.P2<FFx.P2<Nat, Nat>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~Nat, ~Nat, ~Wr.get_nat, d)))))):
  match d:
    case Wr.Got{+v0, +r}:
      +ee = ed
      fd.win.s1(s, v0, r, Wire.wire_nat_exact(s, v0, r, ee), Wire.wire_nat_decoded_fits(s, v0, r, ee), Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def fd.win(+s: String) -> fd.WI(s, FFx.get_win(s)):
  fd.win.s0(s, Wr.get_nat(s), {==})

# Requests, by tag
# ----------------

# a level request: level, user's budgets, defaults
def fd.lvl.s2(+s: String, +v0: Fx.ELv, +v1: Fx.Customs, +s2: String, pre: {s == Wr.put_nat(0n, FactsBudgets.facts_spell_elv(v0, FactsBudgets.facts_spell_customs(v1, s2))) : String}, f1: {FactsBudgets.core_customs_fit(v1) == True{} : Bool}, d: Wr.Dec<Fx.Budgets>, xd: fd.BU(s2, d)) -> fd.Req(s, FFx.get_level.of(FFx.seq.fin(~FFx.P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, FFx.P2{v0, v1}, d))):
  match d:
    case Wr.Got{+v2, +r}:
      (e, fj) = xd
      +f2 = fj
      (fd.step(z => Wr.put_nat(0n, FactsBudgets.facts_spell_elv(v0, FactsBudgets.facts_spell_customs(v1, z))), s, s2, FactsBudgets.facts_spell_budgets(v2, r), pre, e), LAWireSpell.ws_and_tt(FactsBudgets.core_customs_fit(v1), FactsBudgets.core_budgets_fit(v2), f1, f2))
    case Wr.Bad{}:
      Unit{}

def fd.lvl.s1(+s: String, +v0: Fx.ELv, +s1: String, pre: {s == Wr.put_nat(0n, FactsBudgets.facts_spell_elv(v0, s1)) : String}, d: Wr.Dec<Fx.Customs>, xd: fd.CU(s1, d)) -> fd.Req(s, FFx.get_level.of(FFx.seq(~FFx.P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq.fin(~Fx.ELv, ~Fx.Customs, v0, d)))):
  match d:
    case Wr.Got{+v1, +r}:
      (e, fj) = xd
      fd.lvl.s2(s, v0, v1, r, fd.step(z => Wr.put_nat(0n, FactsBudgets.facts_spell_elv(v0, z)), s, s1, FactsBudgets.facts_spell_customs(v1, r), pre, e), fj, FFx.get_budgets(r), fd.bud(r))
    case Wr.Bad{}:
      Unit{}

def fd.lvl.s0(+s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<Fx.ELv>, xd: fd.EL(s0, d)) -> fd.Req(s, FFx.get_level.of(FFx.seq(~FFx.P2<Fx.ELv, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq(~Fx.ELv, ~Fx.Customs, ~FFx.get_customs, d)))):
  match d:
    case Wr.Got{+v0, +r}:
      fd.lvl.s1(s, v0, r, fd.step(z => Wr.put_nat(0n, z), s, s0, FactsBudgets.facts_spell_elv(v0, r), pre, xd), FFx.get_customs(r), fd.cus(r))
    case Wr.Bad{}:
      Unit{}

# a room request: budget, ceiling, answer
def fd.room.s2(+s: String, +v0: Nat, +v1: Nat, +s2: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(v0, Wr.put_nat(v1, s2))) : String}, f0: {LawsBase.wire_fits(v0) == True{} : Bool}, f1: {LawsBase.wire_fits(v1) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> fd.Req(s, FFx.get_room.of(FFx.seq.fin(~FFx.P2<Nat, Nat>, ~Nat, FFx.P2{v0, v1}, d))):
  match d:
    case Wr.Got{+v2, +r}:
      +ee = ed
      +f2 = Wire.wire_nat_decoded_fits(s2, v2, r, ee)
      (fd.step(z => Wr.put_nat(1n, Wr.put_nat(v0, Wr.put_nat(v1, z))), s, s2, Wr.put_nat(v2, r), pre, Wire.wire_nat_exact(s2, v2, r, ee)), LAWireSpell.ws_and_tt(LawsBase.wire_fits(v0), Bool.and(LawsBase.wire_fits(v1), LawsBase.wire_fits(v2)), f0, LAWireSpell.ws_and_tt(LawsBase.wire_fits(v1), LawsBase.wire_fits(v2), f1, f2)))
    case Wr.Bad{}:
      Unit{}

def fd.room.s1(+s: String, +v0: Nat, +s1: String, pre: {s == Wr.put_nat(1n, Wr.put_nat(v0, s1)) : String}, f0: {LawsBase.wire_fits(v0) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> fd.Req(s, FFx.get_room.of(FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~Nat, ~Nat, v0, d)))):
  match d:
    case Wr.Got{+v1, +r}:
      +ee = ed
      fd.room.s2(s, v0, v1, r, fd.step(z => Wr.put_nat(1n, Wr.put_nat(v0, z)), s, s1, Wr.put_nat(v1, r), pre, Wire.wire_nat_exact(s1, v1, r, ee)), f0, Wire.wire_nat_decoded_fits(s1, v1, r, ee), Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def fd.room.s0(+s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s0) == d : Wr.Dec<Nat>}) -> fd.Req(s, FFx.get_room.of(FFx.seq(~FFx.P2<Nat, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~Nat, ~Nat, ~Wr.get_nat, d)))):
  match d:
    case Wr.Got{+v0, +r}:
      +ee = ed
      fd.room.s1(s, v0, r, fd.step(z => Wr.put_nat(1n, z), s, s0, Wr.put_nat(v0, r), pre, Wire.wire_nat_exact(s0, v0, r, ee)), Wire.wire_nat_decoded_fits(s0, v0, r, ee), Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

# an adjust request: caller's cap, model's cap, level, user's budgets, defaults, answer
def fd.adj.s6(+s: String, +v0: Maybe<&2, Nat>, +v1: Nat, +v2: Fx.ELv, +v3: Fx.Customs, +v4: Fx.Budgets, +v5: Nat, +s6: String, pre: {s == Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(v0, Wr.put_nat(v1, FactsBudgets.facts_spell_elv(v2, FactsBudgets.facts_spell_customs(v3, FactsBudgets.facts_spell_budgets(v4, Wr.put_nat(v5, s6))))))) : String}, f0: {LawsBase.core_mfits(v0) == True{} : Bool}, f1: {LawsBase.wire_fits(v1) == True{} : Bool}, f3: {FactsBudgets.core_customs_fit(v3) == True{} : Bool}, f4: {FactsBudgets.core_budgets_fit(v4) == True{} : Bool}, f5: {LawsBase.wire_fits(v5) == True{} : Bool}, d: Wr.Dec<Fx.Win>, xd: fd.WI(s6, d)) -> fd.Req(s, FFx.get_adjust.of(FFx.seq.fin(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, FFx.P2{FFx.P2{FFx.P2{FFx.P2{FFx.P2{v0, v1}, v2}, v3}, v4}, v5}, d))):
  match d:
    case Wr.Got{+v6, +r}:
      (e, fj) = xd
      +f6 = fj
      (fd.step(z => Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(v0, Wr.put_nat(v1, FactsBudgets.facts_spell_elv(v2, FactsBudgets.facts_spell_customs(v3, FactsBudgets.facts_spell_budgets(v4, Wr.put_nat(v5, z))))))), s, s6, FactsBudgets.facts_spell_win(v6, r), pre, e), LAWireSpell.ws_and_tt(LawsBase.core_mfits(v0), Bool.and(LawsBase.wire_fits(v1), Bool.and(FactsBudgets.core_customs_fit(v3), Bool.and(FactsBudgets.core_budgets_fit(v4), Bool.and(LawsBase.wire_fits(v5), FactsBudgets.core_win_fit(v6))))), f0, LAWireSpell.ws_and_tt(LawsBase.wire_fits(v1), Bool.and(FactsBudgets.core_customs_fit(v3), Bool.and(FactsBudgets.core_budgets_fit(v4), Bool.and(LawsBase.wire_fits(v5), FactsBudgets.core_win_fit(v6)))), f1, LAWireSpell.ws_and_tt(FactsBudgets.core_customs_fit(v3), Bool.and(FactsBudgets.core_budgets_fit(v4), Bool.and(LawsBase.wire_fits(v5), FactsBudgets.core_win_fit(v6))), f3, LAWireSpell.ws_and_tt(FactsBudgets.core_budgets_fit(v4), Bool.and(LawsBase.wire_fits(v5), FactsBudgets.core_win_fit(v6)), f4, LAWireSpell.ws_and_tt(LawsBase.wire_fits(v5), FactsBudgets.core_win_fit(v6), f5, f6))))))
    case Wr.Bad{}:
      Unit{}

def fd.adj.s5(+s: String, +v0: Maybe<&2, Nat>, +v1: Nat, +v2: Fx.ELv, +v3: Fx.Customs, +v4: Fx.Budgets, +s5: String, pre: {s == Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(v0, Wr.put_nat(v1, FactsBudgets.facts_spell_elv(v2, FactsBudgets.facts_spell_customs(v3, FactsBudgets.facts_spell_budgets(v4, s5)))))) : String}, f0: {LawsBase.core_mfits(v0) == True{} : Bool}, f1: {LawsBase.wire_fits(v1) == True{} : Bool}, f3: {FactsBudgets.core_customs_fit(v3) == True{} : Bool}, f4: {FactsBudgets.core_budgets_fit(v4) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s5) == d : Wr.Dec<Nat>}) -> fd.Req(s, FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq.fin(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, FFx.P2{FFx.P2{FFx.P2{FFx.P2{v0, v1}, v2}, v3}, v4}, d)))):
  match d:
    case Wr.Got{+v5, +r}:
      +ee = ed
      fd.adj.s6(s, v0, v1, v2, v3, v4, v5, r, fd.step(z => Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(v0, Wr.put_nat(v1, FactsBudgets.facts_spell_elv(v2, FactsBudgets.facts_spell_customs(v3, FactsBudgets.facts_spell_budgets(v4, z)))))), s, s5, Wr.put_nat(v5, r), pre, Wire.wire_nat_exact(s5, v5, r, ee)), f0, f1, f3, f4, Wire.wire_nat_decoded_fits(s5, v5, r, ee), FFx.get_win(r), fd.win(r))
    case Wr.Bad{}:
      Unit{}

def fd.adj.s4(+s: String, +v0: Maybe<&2, Nat>, +v1: Nat, +v2: Fx.ELv, +v3: Fx.Customs, +s4: String, pre: {s == Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(v0, Wr.put_nat(v1, FactsBudgets.facts_spell_elv(v2, FactsBudgets.facts_spell_customs(v3, s4))))) : String}, f0: {LawsBase.core_mfits(v0) == True{} : Bool}, f1: {LawsBase.wire_fits(v1) == True{} : Bool}, f3: {FactsBudgets.core_customs_fit(v3) == True{} : Bool}, d: Wr.Dec<Fx.Budgets>, xd: fd.BU(s4, d)) -> fd.Req(s, FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, FFx.P2{FFx.P2{FFx.P2{v0, v1}, v2}, v3}, d))))):
  match d:
    case Wr.Got{+v4, +r}:
      (e, fj) = xd
      fd.adj.s5(s, v0, v1, v2, v3, v4, r, fd.step(z => Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(v0, Wr.put_nat(v1, FactsBudgets.facts_spell_elv(v2, FactsBudgets.facts_spell_customs(v3, z))))), s, s4, FactsBudgets.facts_spell_budgets(v4, r), pre, e), f0, f1, f3, fj, Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def fd.adj.s3(+s: String, +v0: Maybe<&2, Nat>, +v1: Nat, +v2: Fx.ELv, +s3: String, pre: {s == Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(v0, Wr.put_nat(v1, FactsBudgets.facts_spell_elv(v2, s3)))) : String}, f0: {LawsBase.core_mfits(v0) == True{} : Bool}, f1: {LawsBase.wire_fits(v1) == True{} : Bool}, d: Wr.Dec<Fx.Customs>, xd: fd.CU(s3, d)) -> fd.Req(s, FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq.fin(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, FFx.P2{FFx.P2{v0, v1}, v2}, d)))))):
  match d:
    case Wr.Got{+v3, +r}:
      (e, fj) = xd
      fd.adj.s4(s, v0, v1, v2, v3, r, fd.step(z => Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(v0, Wr.put_nat(v1, FactsBudgets.facts_spell_elv(v2, z)))), s, s3, FactsBudgets.facts_spell_customs(v3, r), pre, e), f0, f1, fj, FFx.get_budgets(r), fd.bud(r))
    case Wr.Bad{}:
      Unit{}

def fd.adj.s2(+s: String, +v0: Maybe<&2, Nat>, +v1: Nat, +s2: String, pre: {s == Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(v0, Wr.put_nat(v1, s2))) : String}, f0: {LawsBase.core_mfits(v0) == True{} : Bool}, f1: {LawsBase.wire_fits(v1) == True{} : Bool}, d: Wr.Dec<Fx.ELv>, xd: fd.EL(s2, d)) -> fd.Req(s, FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, ~FFx.get_customs, FFx.seq.fin(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Fx.ELv, FFx.P2{v0, v1}, d))))))):
  match d:
    case Wr.Got{+v2, +r}:
      fd.adj.s3(s, v0, v1, v2, r, fd.step(z => Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(v0, Wr.put_nat(v1, z))), s, s2, FactsBudgets.facts_spell_elv(v2, r), pre, xd), f0, f1, FFx.get_customs(r), fd.cus(r))
    case Wr.Bad{}:
      Unit{}

def fd.adj.s1(+s: String, +v0: Maybe<&2, Nat>, +s1: String, pre: {s == Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(v0, s1)) : String}, f0: {LawsBase.core_mfits(v0) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> fd.Req(s, FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, ~FFx.get_customs, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Fx.ELv, ~FFx.get_elv, FFx.seq.fin(~Maybe<&2, Nat>, ~Nat, v0, d)))))))):
  match d:
    case Wr.Got{+v1, +r}:
      +ee = ed
      fd.adj.s2(s, v0, v1, r, fd.step(z => Wr.put_nat(2n, FactsBudgets.facts_spell_mnat(v0, z)), s, s1, Wr.put_nat(v1, r), pre, Wire.wire_nat_exact(s1, v1, r, ee)), f0, Wire.wire_nat_decoded_fits(s1, v1, r, ee), FFx.get_elv(r), fd.elv(r))
    case Wr.Bad{}:
      Unit{}

def fd.adj.s0(+s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<Maybe<&2, Nat>>, xd: fd.MN(s0, d)) -> fd.Req(s, FFx.get_adjust.of(FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, Nat>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, Fx.Customs>, ~Fx.Budgets, ~FFx.get_budgets, FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Fx.ELv>, ~Fx.Customs, ~FFx.get_customs, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Fx.ELv, ~FFx.get_elv, FFx.seq(~Maybe<&2, Nat>, ~Nat, ~Wr.get_nat, d)))))))):
  match d:
    case Wr.Got{+v0, +r}:
      (e, fj) = xd
      fd.adj.s1(s, v0, r, fd.step(z => Wr.put_nat(2n, z), s, s0, FactsBudgets.facts_spell_mnat(v0, r), pre, e), fj, Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

# a Google request: rule, user's budgets, budget level
def fd.ggl.s2(+s: String, +v0: Maybe<&2, Fx.Budgets>, +v1: Fx.Customs, +s2: String, pre: {s == Wr.put_nat(3n, FactsBudgets.facts_spell_mbudgets(v0, FactsBudgets.facts_spell_customs(v1, s2))) : String}, f0: {FactsBudgets.core_mbudgets_fit(v0) == True{} : Bool}, f1: {FactsBudgets.core_customs_fit(v1) == True{} : Bool}, d: Wr.Dec<Fx.Lv>, xd: fd.LV(s2, d)) -> fd.Req(s, FFx.get_google.of(FFx.seq.fin(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, FFx.P2{v0, v1}, d))):
  match d:
    case Wr.Got{+v2, +r}:
      (fd.step(z => Wr.put_nat(3n, FactsBudgets.facts_spell_mbudgets(v0, FactsBudgets.facts_spell_customs(v1, z))), s, s2, FactsBudgets.facts_spell_lv(v2, r), pre, xd), LAWireSpell.ws_and_tt(FactsBudgets.core_mbudgets_fit(v0), FactsBudgets.core_customs_fit(v1), f0, f1))
    case Wr.Bad{}:
      Unit{}

def fd.ggl.s1(+s: String, +v0: Maybe<&2, Fx.Budgets>, +s1: String, pre: {s == Wr.put_nat(3n, FactsBudgets.facts_spell_mbudgets(v0, s1)) : String}, f0: {FactsBudgets.core_mbudgets_fit(v0) == True{} : Bool}, d: Wr.Dec<Fx.Customs>, xd: fd.CU(s1, d)) -> fd.Req(s, FFx.get_google.of(FFx.seq(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, ~FFx.get_lv, FFx.seq.fin(~Maybe<&2, Fx.Budgets>, ~Fx.Customs, v0, d)))):
  match d:
    case Wr.Got{+v1, +r}:
      (e, fj) = xd
      fd.ggl.s2(s, v0, v1, r, fd.step(z => Wr.put_nat(3n, FactsBudgets.facts_spell_mbudgets(v0, z)), s, s1, FactsBudgets.facts_spell_customs(v1, r), pre, e), f0, fj, FFx.get_lv(r), fd.lv(r))
    case Wr.Bad{}:
      Unit{}

def fd.ggl.s0(+s: String, +s0: String, pre: {s == Wr.put_nat(3n, s0) : String}, d: Wr.Dec<Maybe<&2, Fx.Budgets>>, xd: fd.MB(s0, d)) -> fd.Req(s, FFx.get_google.of(FFx.seq(~FFx.P2<Maybe<&2, Fx.Budgets>, Fx.Customs>, ~Fx.Lv, ~FFx.get_lv, FFx.seq(~Maybe<&2, Fx.Budgets>, ~Fx.Customs, ~FFx.get_customs, d)))):
  match d:
    case Wr.Got{+v0, +r}:
      (e, fj) = xd
      fd.ggl.s1(s, v0, r, fd.step(z => Wr.put_nat(3n, z), s, s0, FactsBudgets.facts_spell_mbudgets(v0, r), pre, e), fj, FFx.get_customs(r), fd.cus(r))
    case Wr.Bad{}:
      Unit{}

# an aux request: user's budgets, defaults, answer, top
def fd.aux.s3(+s: String, +v0: Fx.Customs, +v1: Fx.Budgets, +v2: Nat, +s3: String, pre: {s == Wr.put_nat(4n, FactsBudgets.facts_spell_customs(v0, FactsBudgets.facts_spell_budgets(v1, Wr.put_nat(v2, s3)))) : String}, f0: {FactsBudgets.core_customs_fit(v0) == True{} : Bool}, f1: {FactsBudgets.core_budgets_fit(v1) == True{} : Bool}, f2: {LawsBase.wire_fits(v2) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s3) == d : Wr.Dec<Nat>}) -> fd.Req(s, FFx.get_aux.of(FFx.seq.fin(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, FFx.P2{FFx.P2{v0, v1}, v2}, d))):
  match d:
    case Wr.Got{+v3, +r}:
      +ee = ed
      +f3 = Wire.wire_nat_decoded_fits(s3, v3, r, ee)
      (fd.step(z => Wr.put_nat(4n, FactsBudgets.facts_spell_customs(v0, FactsBudgets.facts_spell_budgets(v1, Wr.put_nat(v2, z)))), s, s3, Wr.put_nat(v3, r), pre, Wire.wire_nat_exact(s3, v3, r, ee)), LAWireSpell.ws_and_tt(FactsBudgets.core_customs_fit(v0), Bool.and(FactsBudgets.core_budgets_fit(v1), Bool.and(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3))), f0, LAWireSpell.ws_and_tt(FactsBudgets.core_budgets_fit(v1), Bool.and(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3)), f1, LAWireSpell.ws_and_tt(LawsBase.wire_fits(v2), LawsBase.wire_fits(v3), f2, f3))))
    case Wr.Bad{}:
      Unit{}

def fd.aux.s2(+s: String, +v0: Fx.Customs, +v1: Fx.Budgets, +s2: String, pre: {s == Wr.put_nat(4n, FactsBudgets.facts_spell_customs(v0, FactsBudgets.facts_spell_budgets(v1, s2))) : String}, f0: {FactsBudgets.core_customs_fit(v0) == True{} : Bool}, f1: {FactsBudgets.core_budgets_fit(v1) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s2) == d : Wr.Dec<Nat>}) -> fd.Req(s, FFx.get_aux.of(FFx.seq(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~FFx.P2<Fx.Customs, Fx.Budgets>, ~Nat, FFx.P2{v0, v1}, d)))):
  match d:
    case Wr.Got{+v2, +r}:
      +ee = ed
      fd.aux.s3(s, v0, v1, v2, r, fd.step(z => Wr.put_nat(4n, FactsBudgets.facts_spell_customs(v0, FactsBudgets.facts_spell_budgets(v1, z))), s, s2, Wr.put_nat(v2, r), pre, Wire.wire_nat_exact(s2, v2, r, ee)), f0, f1, Wire.wire_nat_decoded_fits(s2, v2, r, ee), Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def fd.aux.s1(+s: String, +v0: Fx.Customs, +s1: String, pre: {s == Wr.put_nat(4n, FactsBudgets.facts_spell_customs(v0, s1)) : String}, f0: {FactsBudgets.core_customs_fit(v0) == True{} : Bool}, d: Wr.Dec<Fx.Budgets>, xd: fd.BU(s1, d)) -> fd.Req(s, FFx.get_aux.of(FFx.seq(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Fx.Customs, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq.fin(~Fx.Customs, ~Fx.Budgets, v0, d))))):
  match d:
    case Wr.Got{+v1, +r}:
      (e, fj) = xd
      fd.aux.s2(s, v0, v1, r, fd.step(z => Wr.put_nat(4n, FactsBudgets.facts_spell_customs(v0, z)), s, s1, FactsBudgets.facts_spell_budgets(v1, r), pre, e), f0, fj, Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def fd.aux.s0(+s: String, +s0: String, pre: {s == Wr.put_nat(4n, s0) : String}, d: Wr.Dec<Fx.Customs>, xd: fd.CU(s0, d)) -> fd.Req(s, FFx.get_aux.of(FFx.seq(~FFx.P2<FFx.P2<Fx.Customs, Fx.Budgets>, Nat>, ~Nat, ~Wr.get_nat, FFx.seq(~FFx.P2<Fx.Customs, Fx.Budgets>, ~Nat, ~Wr.get_nat, FFx.seq(~Fx.Customs, ~Fx.Budgets, ~FFx.get_budgets, d))))):
  match d:
    case Wr.Got{+v0, +r}:
      (e, fj) = xd
      fd.aux.s1(s, v0, r, fd.step(z => Wr.put_nat(4n, z), s, s0, FactsBudgets.facts_spell_customs(v0, r), pre, e), fj, FFx.get_budgets(r), fd.bud(r))
    case Wr.Bad{}:
      Unit{}

# a cap request: caller's cap, model's cap, needs, window facts
def fd.cap.s3(+s: String, +v0: Maybe<&2, Nat>, +v1: Nat, +v2: Bool, +s3: String, pre: {s == Wr.put_nat(5n, FactsBudgets.facts_spell_mnat(v0, Wr.put_nat(v1, Wr.put_bool(v2, s3)))) : String}, f0: {LawsBase.core_mfits(v0) == True{} : Bool}, f1: {LawsBase.wire_fits(v1) == True{} : Bool}, d: Wr.Dec<Fx.Win>, xd: fd.WI(s3, d)) -> fd.Req(s, FFx.get_cap.of(FFx.seq.fin(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Bool>, ~Fx.Win, FFx.P2{FFx.P2{v0, v1}, v2}, d))):
  match d:
    case Wr.Got{+v3, +r}:
      (e, fj) = xd
      +f3 = fj
      (fd.step(z => Wr.put_nat(5n, FactsBudgets.facts_spell_mnat(v0, Wr.put_nat(v1, Wr.put_bool(v2, z)))), s, s3, FactsBudgets.facts_spell_win(v3, r), pre, e), LAWireSpell.ws_and_tt(LawsBase.core_mfits(v0), Bool.and(LawsBase.wire_fits(v1), FactsBudgets.core_win_fit(v3)), f0, LAWireSpell.ws_and_tt(LawsBase.wire_fits(v1), FactsBudgets.core_win_fit(v3), f1, f3)))
    case Wr.Bad{}:
      Unit{}

def fd.cap.s2(+s: String, +v0: Maybe<&2, Nat>, +v1: Nat, +s2: String, pre: {s == Wr.put_nat(5n, FactsBudgets.facts_spell_mnat(v0, Wr.put_nat(v1, s2))) : String}, f0: {LawsBase.core_mfits(v0) == True{} : Bool}, f1: {LawsBase.wire_fits(v1) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> fd.Req(s, FFx.get_cap.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Bool>, ~Fx.Win, ~FFx.get_win, FFx.seq.fin(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Bool, FFx.P2{v0, v1}, d)))):
  match d:
    case Wr.Got{+v2, +r}:
      +ee = ed
      fd.cap.s3(s, v0, v1, v2, r, fd.step(z => Wr.put_nat(5n, FactsBudgets.facts_spell_mnat(v0, Wr.put_nat(v1, z))), s, s2, Wr.put_bool(v2, r), pre, Wire.wire_bool_exact(s2, v2, r, ee)), f0, f1, FFx.get_win(r), fd.win(r))
    case Wr.Bad{}:
      Unit{}

def fd.cap.s1(+s: String, +v0: Maybe<&2, Nat>, +s1: String, pre: {s == Wr.put_nat(5n, FactsBudgets.facts_spell_mnat(v0, s1)) : String}, f0: {LawsBase.core_mfits(v0) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> fd.Req(s, FFx.get_cap.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Bool>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Bool, ~Wr.get_bool, FFx.seq.fin(~Maybe<&2, Nat>, ~Nat, v0, d))))):
  match d:
    case Wr.Got{+v1, +r}:
      +ee = ed
      fd.cap.s2(s, v0, v1, r, fd.step(z => Wr.put_nat(5n, FactsBudgets.facts_spell_mnat(v0, z)), s, s1, Wr.put_nat(v1, r), pre, Wire.wire_nat_exact(s1, v1, r, ee)), f0, Wire.wire_nat_decoded_fits(s1, v1, r, ee), Wr.get_bool(r), {==})
    case Wr.Bad{}:
      Unit{}

def fd.cap.s0(+s: String, +s0: String, pre: {s == Wr.put_nat(5n, s0) : String}, d: Wr.Dec<Maybe<&2, Nat>>, xd: fd.MN(s0, d)) -> fd.Req(s, FFx.get_cap.of(FFx.seq(~FFx.P2<FFx.P2<Maybe<&2, Nat>, Nat>, Bool>, ~Fx.Win, ~FFx.get_win, FFx.seq(~FFx.P2<Maybe<&2, Nat>, Nat>, ~Bool, ~Wr.get_bool, FFx.seq(~Maybe<&2, Nat>, ~Nat, ~Wr.get_nat, d))))):
  match d:
    case Wr.Got{+v0, +r}:
      (e, fj) = xd
      fd.cap.s1(s, v0, r, fd.step(z => Wr.put_nat(5n, z), s, s0, FactsBudgets.facts_spell_mnat(v0, r), pre, e), fj, Wr.get_nat(r), {==})
    case Wr.Bad{}:
      Unit{}

def fd.req.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> fd.Req(s, FFx.get_req.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          fd.lvl.s0(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), FFx.get_elv(s0), fd.elv(s0))
        case 1n:
          fd.room.s0(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_nat(s0), {==})
        case 2n:
          fd.adj.s0(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), FFx.get_mnat(s0), fd.mnat(s0))
        case 3n:
          fd.ggl.s0(s, s0, Wire.wire_nat_exact(s, 3n, s0, ed), FFx.get_mbudgets(s0), fd.mb(s0))
        case 4n:
          fd.aux.s0(s, s0, Wire.wire_nat_exact(s, 4n, s0, ed), FFx.get_customs(s0), fd.cus(s0))
        case 5n:
          fd.cap.s0(s, s0, Wire.wire_nat_exact(s, 5n, s0, ed), FFx.get_mnat(s0), fd.mnat(s0))
        case 6n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# whatever the entry's decoder reads is a spelled request that fits, then
# the rest
def fd.req(+s: String) -> fd.Req(s, FFx.get_req(s)):
  fd.req.go(s, Wr.get_nat(s), {==})

# The entry
# ---------

def fro.G(s: String, a: String) -> Type:
  Sigma<&1, &1, FFx.Req, q => {(s, (FactsBudgets.core_facts_req_fits(q), a)) == (FactsBudgets.facts_spell_req(q, ""), (True{}, FactsBudgets.facts_spell_answer(q))) : String & (Bool & String)}>

# a request read whole: the input, the fit and the answer are the spec's
def fro.top_eq(+s: String, +q: FFx.Req, +a: String, e: {s == FactsBudgets.facts_spell_req(q, "") : String}, f: {FactsBudgets.core_facts_req_fits(q) == True{} : Bool}, ea: {a == FactsBudgets.facts_spell_answer(q) : String}) -> {(s, (FactsBudgets.core_facts_req_fits(q), a)) == (FactsBudgets.facts_spell_req(q, ""), (True{}, FactsBudgets.facts_spell_answer(q))) : String & (Bool & String)}:
  %Equal.sym(String, s, FactsBudgets.facts_spell_req(q, ""), e) : {(_, (FactsBudgets.core_facts_req_fits(q), a)) == (FactsBudgets.facts_spell_req(q, ""), (True{}, FactsBudgets.facts_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(Bool, FactsBudgets.core_facts_req_fits(q), True{}, f) : {(FactsBudgets.facts_spell_req(q, ""), (_, a)) == (FactsBudgets.facts_spell_req(q, ""), (True{}, FactsBudgets.facts_spell_answer(q))) : String & (Bool & String)}
  %Equal.sym(String, a, FactsBudgets.facts_spell_answer(q), ea) : {(FactsBudgets.facts_spell_req(q, ""), (True{}, _)) == (FactsBudgets.facts_spell_req(q, ""), (True{}, FactsBudgets.facts_spell_answer(q))) : String & (Bool & String)}
  {==}

# the end check: nothing left answers the request, anything left is the
# error form
def fro.fin(+s: String, +q: FFx.Req, r: String, pre: {s == FactsBudgets.facts_spell_req(q, r) : String}, f: {FactsBudgets.core_facts_req_fits(q) == True{} : Bool}, ok: {LawsBase.wire_opens_err(FFx.ffi.done(Wr.end(r), q)) == False{} : Bool}) -> fro.G(s, FFx.ffi.done(Wr.end(r), q)):
  match r:
    case SNil{}:
      (q, fro.top_eq(s, q, FFx.ffi.done(True{}, q), pre, f, LA.fs.answer(q)))
    case SCon{x, y}:
      LAWireSpell.ws_absurd(fro.G(s, FFx.ffi.done(False{}, q)), ok)

def fro.main(+s: String, d: Wr.Dec<FFx.Req>, inv: fd.Req(s, d), ok: {LawsBase.wire_opens_err(FFx.ffi.go(d)) == False{} : Bool}) -> fro.G(s, FFx.ffi.go(d)):
  match d:
    case Wr.Got{+q, +r}:
      (e, f) = inv
      fro.fin(s, q, r, e, f, ok)
    case Wr.Bad{}:
      LAWireSpell.ws_absurd(fro.G(s, Wr.err("budget request: malformed")), ok)

def FactsBudgets.core_facts_reads_only_requests(s, ok):
  fro.main(s, FFx.get_req(s), fd.req(s), ok)
