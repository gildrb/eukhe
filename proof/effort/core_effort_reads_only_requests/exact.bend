# eukhe: the entry's decoders read only spelled values
#
# Whatever a decoder of bend/ffi_effort.bend reads is the laws' spelling
# (laws/effort.bend core_effort_spell_*) of what it read, then its rest,
# and the counts fit: a tag by the wire's exactness law (wire_nat_exact;
# an unknown tag is Bad), a Bool by wire_bool_exact, a list by its count
# (wire_nat_exact, wire_nat_decoded_fits) and item by item, a record (a
# map, the facts, a request) stage by stage along the entry's seq, the
# equation of the input so far carried in a predicate per stage (ex.M*,
# ex.F*, ex.C*).

import Base
import ../../../bend/effort.bend as Ef
import ../../../bend/ffi_effort.bend as FEf
import ../../../bend/wire.bend as Wr
import ../../../laws/effort.bend as Effort
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../wire/base/spell.bend as LAWireSpell

# s spelled up to a field a is s spelled up to its spelling b
def ex.step(-F: String -> String, -s: String, -a: String, -b: String, pre: {s == F(a) : String}, e: {a == b : String}) -> {s == F(b) : String}:
  Equal.trans(String, s, F(a), F(b), pre, Equal.cong(String, String, F, a, b, e))

# Tags
# ----

def ex.Lv(s: String, d: Wr.Dec<Ef.Lv>) -> Type:
  match d:
    case Wr.Got{l, r}:
      {s == Effort.core_effort_spell_lv(l, r) : String}
    case Wr.Bad{}:
      Unit

def ex.lv.tag(-s: String, t: Nat, -s0: String, en: {s == Wr.put_nat(t, s0) : String}) -> ex.Lv(s, FEf.get_lv.tag(t, s0)):
  match t:
    case 0n:
      en
    case 1n:
      en
    case 2n:
      en
    case 3n:
      en
    case 4n:
      en
    case 5n:
      en
    case 6n:
      en
    case 7n+k:
      Unit{}

def ex.lv.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ex.Lv(s, FEf.get_lv.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      ex.lv.tag(s, t, s0, Wire.wire_nat_exact(s, t, s0, ed))
    case Wr.Bad{}:
      Unit{}

def ex.lv(+s: String) -> ex.Lv(s, FEf.get_lv(s)):
  ex.lv.go(s, Wr.get_nat(s), {==})

def ex.Ent(s: String, d: Wr.Dec<Ef.Ent>) -> Type:
  match d:
    case Wr.Got{e, r}:
      {s == Effort.core_effort_spell_ent(e, r) : String}
    case Wr.Bad{}:
      Unit

def ex.ent.tag(-s: String, t: Nat, -s0: String, en: {s == Wr.put_nat(t, s0) : String}) -> ex.Ent(s, FEf.get_ent.tag(t, s0)):
  match t:
    case 0n:
      en
    case 1n:
      en
    case 2n:
      en
    case 3n+k:
      Unit{}

def ex.ent.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ex.Ent(s, FEf.get_ent.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      ex.ent.tag(s, t, s0, Wire.wire_nat_exact(s, t, s0, ed))
    case Wr.Bad{}:
      Unit{}

def ex.ent(+s: String) -> ex.Ent(s, FEf.get_ent(s)):
  ex.ent.go(s, Wr.get_nat(s), {==})

def ex.Dir(s: String, d: Wr.Dec<Ef.Dir>) -> Type:
  match d:
    case Wr.Got{x, r}:
      {s == Effort.core_effort_spell_dir(x, r) : String}
    case Wr.Bad{}:
      Unit

def ex.dir.tag(-s: String, t: Nat, -s0: String, en: {s == Wr.put_nat(t, s0) : String}) -> ex.Dir(s, FEf.get_dir.tag(t, s0)):
  match t:
    case 0n:
      en
    case 1n:
      en
    case 2n+k:
      Unit{}

def ex.dir.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ex.Dir(s, FEf.get_dir.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      ex.dir.tag(s, t, s0, Wire.wire_nat_exact(s, t, s0, ed))
    case Wr.Bad{}:
      Unit{}

def ex.dir(+s: String) -> ex.Dir(s, FEf.get_dir(s)):
  ex.dir.go(s, Wr.get_nat(s), {==})

def ex.Bool(s: String, d: Wr.Dec<Bool>) -> Type:
  match d:
    case Wr.Got{b, r}:
      {s == Wr.put_bool(b, r) : String}
    case Wr.Bad{}:
      Unit

def ex.bool.go(+s: String, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s) == d : Wr.Dec<Bool>}) -> ex.Bool(s, d):
  match d:
    case Wr.Got{+b, +r}:
      Wire.wire_bool_exact(s, b, r, ed)
    case Wr.Bad{}:
      Unit{}

def ex.bool(+s: String) -> ex.Bool(s, Wr.get_bool(s)):
  ex.bool.go(s, Wr.get_bool(s), {==})

# A map: seven entries along the entry's seq
# ------------------------------------------

def ex.m2(q: FEf.P2<Ef.Ent, Ef.Ent>, r: String) -> String:
  match q:
    case FEf.P2{a, b}:
      Effort.core_effort_spell_ent(a, Effort.core_effort_spell_ent(b, r))

def ex.m3(q: FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, r: String) -> String:
  match q:
    case FEf.P2{a, b}:
      ex.m2(a, Effort.core_effort_spell_ent(b, r))

def ex.m4(q: FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, r: String) -> String:
  match q:
    case FEf.P2{a, b}:
      ex.m3(a, Effort.core_effort_spell_ent(b, r))

def ex.m5(q: FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, r: String) -> String:
  match q:
    case FEf.P2{a, b}:
      ex.m4(a, Effort.core_effort_spell_ent(b, r))

def ex.m6(q: FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, r: String) -> String:
  match q:
    case FEf.P2{a, b}:
      ex.m5(a, Effort.core_effort_spell_ent(b, r))

def ex.m7(q: FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, r: String) -> String:
  match q:
    case FEf.P2{a, b}:
      ex.m6(a, Effort.core_effort_spell_ent(b, r))

def ex.M2(s: String, d: Wr.Dec<FEf.P2<Ef.Ent, Ef.Ent>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ex.m2(q, r) : String}
    case Wr.Bad{}:
      Unit

def ex.M3(s: String, d: Wr.Dec<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ex.m3(q, r) : String}
    case Wr.Bad{}:
      Unit

def ex.M4(s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ex.m4(q, r) : String}
    case Wr.Bad{}:
      Unit

def ex.M5(s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ex.m5(q, r) : String}
    case Wr.Bad{}:
      Unit

def ex.M6(s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ex.m6(q, r) : String}
    case Wr.Bad{}:
      Unit

def ex.M7(s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ex.m7(q, r) : String}
    case Wr.Bad{}:
      Unit

def ex.mf2(-s: String, +a: Ef.Ent, -r: String, pre: {s == Effort.core_effort_spell_ent(a, r) : String}, e: Wr.Dec<Ef.Ent>, inv: ex.Ent(r, e)) -> ex.M2(s, FEf.seq.fin(~Ef.Ent, ~Ef.Ent, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      ex.step(z => Effort.core_effort_spell_ent(a, z), s, r, Effort.core_effort_spell_ent(b, r2), pre, inv)
    case Wr.Bad{}:
      Unit{}

def ex.ms2(-s: String, d: Wr.Dec<Ef.Ent>, inv: ex.Ent(s, d)) -> ex.M2(s, FEf.seq(~Ef.Ent, ~Ef.Ent, ~FEf.get_ent, d)):
  match d:
    case Wr.Got{+a, +r}:
      ex.mf2(s, a, r, inv, FEf.get_ent(r), ex.ent(r))
    case Wr.Bad{}:
      Unit{}

def ex.mf3(-s: String, +a: FEf.P2<Ef.Ent, Ef.Ent>, -r: String, pre: {s == ex.m2(a, r) : String}, e: Wr.Dec<Ef.Ent>, inv: ex.Ent(r, e)) -> ex.M3(s, FEf.seq.fin(~FEf.P2<Ef.Ent, Ef.Ent>, ~Ef.Ent, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      ex.step(z => ex.m2(a, z), s, r, Effort.core_effort_spell_ent(b, r2), pre, inv)
    case Wr.Bad{}:
      Unit{}

def ex.ms3(-s: String, d: Wr.Dec<FEf.P2<Ef.Ent, Ef.Ent>>, inv: ex.M2(s, d)) -> ex.M3(s, FEf.seq(~FEf.P2<Ef.Ent, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d)):
  match d:
    case Wr.Got{+a, +r}:
      ex.mf3(s, a, r, inv, FEf.get_ent(r), ex.ent(r))
    case Wr.Bad{}:
      Unit{}

def ex.mf4(-s: String, +a: FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, -r: String, pre: {s == ex.m3(a, r) : String}, e: Wr.Dec<Ef.Ent>, inv: ex.Ent(r, e)) -> ex.M4(s, FEf.seq.fin(~FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, ~Ef.Ent, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      ex.step(z => ex.m3(a, z), s, r, Effort.core_effort_spell_ent(b, r2), pre, inv)
    case Wr.Bad{}:
      Unit{}

def ex.ms4(-s: String, d: Wr.Dec<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>>, inv: ex.M3(s, d)) -> ex.M4(s, FEf.seq(~FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d)):
  match d:
    case Wr.Got{+a, +r}:
      ex.mf4(s, a, r, inv, FEf.get_ent(r), ex.ent(r))
    case Wr.Bad{}:
      Unit{}

def ex.mf5(-s: String, +a: FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, -r: String, pre: {s == ex.m4(a, r) : String}, e: Wr.Dec<Ef.Ent>, inv: ex.Ent(r, e)) -> ex.M5(s, FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      ex.step(z => ex.m4(a, z), s, r, Effort.core_effort_spell_ent(b, r2), pre, inv)
    case Wr.Bad{}:
      Unit{}

def ex.ms5(-s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>>, inv: ex.M4(s, d)) -> ex.M5(s, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d)):
  match d:
    case Wr.Got{+a, +r}:
      ex.mf5(s, a, r, inv, FEf.get_ent(r), ex.ent(r))
    case Wr.Bad{}:
      Unit{}

def ex.mf6(-s: String, +a: FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, -r: String, pre: {s == ex.m5(a, r) : String}, e: Wr.Dec<Ef.Ent>, inv: ex.Ent(r, e)) -> ex.M6(s, FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      ex.step(z => ex.m5(a, z), s, r, Effort.core_effort_spell_ent(b, r2), pre, inv)
    case Wr.Bad{}:
      Unit{}

def ex.ms6(-s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>>, inv: ex.M5(s, d)) -> ex.M6(s, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d)):
  match d:
    case Wr.Got{+a, +r}:
      ex.mf6(s, a, r, inv, FEf.get_ent(r), ex.ent(r))
    case Wr.Bad{}:
      Unit{}

def ex.mf7(-s: String, +a: FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, -r: String, pre: {s == ex.m6(a, r) : String}, e: Wr.Dec<Ef.Ent>, inv: ex.Ent(r, e)) -> ex.M7(s, FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      ex.step(z => ex.m6(a, z), s, r, Effort.core_effort_spell_ent(b, r2), pre, inv)
    case Wr.Bad{}:
      Unit{}

def ex.ms7(-s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>>, inv: ex.M6(s, d)) -> ex.M7(s, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d)):
  match d:
    case Wr.Got{+a, +r}:
      ex.mf7(s, a, r, inv, FEf.get_ent(r), ex.ent(r))
    case Wr.Bad{}:
      Unit{}

def ex.Map(s: String, d: Wr.Dec<Ef.LvMap>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Effort.core_effort_spell_map(m, r) : String}
    case Wr.Bad{}:
      Unit

def ex.map.of(-s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>>, inv: ex.M7(s, d)) -> ex.Map(s, FEf.get_map.of(d)):
  match d:
    case Wr.Got{q, r}:
      match q:
        case FEf.P2{q6, mx}:
          match q6:
            case FEf.P2{q5, xh}:
              match q5:
                case FEf.P2{q4, hi}:
                  match q4:
                    case FEf.P2{q3, me}:
                      match q3:
                        case FEf.P2{q2, lo}:
                          match q2:
                            case FEf.P2{o, mi}:
                              inv
    case Wr.Bad{}:
      Unit{}

def ex.map(+s: String) -> ex.Map(s, FEf.get_map(s)):
  +d1 = FEf.get_ent(s)
  +d2 = FEf.seq(~Ef.Ent, ~Ef.Ent, ~FEf.get_ent, d1)
  +d3 = FEf.seq(~FEf.P2<Ef.Ent, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d2)
  +d4 = FEf.seq(~FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d3)
  +d5 = FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d4)
  +d6 = FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d5)
  +d7 = FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, d6)
  ex.map.of(s, d7, ex.ms7(s, d6, ex.ms6(s, d5, ex.ms5(s, d4, ex.ms4(s, d3, ex.ms3(s, d2, ex.ms2(s, d1, ex.ent(s))))))))

def ex.MMap(s: String, d: Wr.Dec<Maybe<&2, Ef.LvMap>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == Effort.core_effort_spell_mmap(m, r) : String}
    case Wr.Bad{}:
      Unit

def ex.mmap.some(-s: String, -s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<Ef.LvMap>, inv: ex.Map(s0, d)) -> ex.MMap(s, FEf.get_mmap.some(d)):
  match d:
    case Wr.Got{+m, +r}:
      ex.step(z => Wr.put_nat(1n, z), s, s0, Effort.core_effort_spell_map(m, r), pre, inv)
    case Wr.Bad{}:
      Unit{}

def ex.mmap.tag(-s: String, t: Nat, +s0: String, en: {s == Wr.put_nat(t, s0) : String}) -> ex.MMap(s, FEf.get_mmap.tag(t, s0)):
  match t:
    case 0n:
      en
    case 1n:
      ex.mmap.some(s, s0, en, FEf.get_map(s0), ex.map(s0))
    case 2n+k:
      Unit{}

def ex.mmap.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ex.MMap(s, FEf.get_mmap.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      ex.mmap.tag(s, t, s0, Wire.wire_nat_exact(s, t, s0, ed))
    case Wr.Bad{}:
      Unit{}

def ex.mmap(+s: String) -> ex.MMap(s, FEf.get_mmap(s)):
  ex.mmap.go(s, Wr.get_nat(s), {==})

# A list of levels: its count, then item by item
# ----------------------------------------------

# what the item loop's answer says about its input s (m + 1 levels)
def ex.Tl(s: String, m: Nat, d: Wr.Dec<List<&2, Ef.Lv>>) -> Type:
  match d:
    case Wr.Got{t, r}:
      {s == Effort.core_effort_spell_lvs.items(t, r) : String} & {List.length(&2, Ef.Lv, t) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def ex.tl.at(+s: String, -d: Wr.Dec<Ef.Lv>, er: {FEf.get_lv(s) == d : Wr.Dec<Ef.Lv>}) -> ex.Lv(s, d):
  %er : ex.Lv(s, _)
  ex.lv(s)

def ex.tl.step(-s: String, +x: Ef.Lv, +s3: String, -k: Nat, ea: {s == Effort.core_effort_spell_lv(x, s3) : String},
  d: Wr.Dec<List<&2, Ef.Lv>>, ih: ex.Tl(s3, k, d)) -> ex.Tl(s, 1n+k, Wr.get_list.cons(Ef.Lv, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (ex.step(z => Effort.core_effort_spell_lv(x, z), s, s3, Effort.core_effort_spell_lvs.items(ys, r), ea, e1),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, Ef.Lv, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only spelled levels
def ex.tl(m: Nat, cur: Wr.Dec<Ef.Lv>, +s: String, er: {FEf.get_lv(s) == cur : Wr.Dec<Ef.Lv>}) ->
  ex.Tl(s, m, Wr.get_list.go(~Ef.Lv, ~FEf.get_lv, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (ex.tl.at(s, Wr.Got{x, s3}, er), {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      ex.tl.step(s, x, s3, k, ex.tl.at(s, Wr.Got{x, s3}, er),
        Wr.get_list.go(~Ef.Lv, ~FEf.get_lv, k, FEf.get_lv(s3)), ex.tl(k, FEf.get_lv(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder's answer says about its input s
def ex.Lvs(s: String, d: Wr.Dec<List<&2, Ef.Lv>>) -> Type:
  match d:
    case Wr.Got{t, r}:
      {s == Effort.core_effort_spell_lvs(t, r) : String} & {Effort.core_lvs_fit(t) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.lvs.eq(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, +t: List<&2, Ef.Lv>, -r: String,
  e1: {s2 == Effort.core_effort_spell_lvs.items(t, r) : String}, e2: {List.length(&2, Ef.Lv, t) == 1n+m : Nat}) -> {s == Effort.core_effort_spell_lvs(t, r) : String}:
  %Equal.sym(Nat, List.length(&2, Ef.Lv, t), 1n+m, e2) : {s == Wr.put_nat(_, Effort.core_effort_spell_lvs.items(t, r)) : String}
  %e1 : {s == Wr.put_nat(1n+m, _) : String}
  en

def ex.lvs.fit(-m: Nat, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, +t: List<&2, Ef.Lv>, e2: {List.length(&2, Ef.Lv, t) == 1n+m : Nat}) -> {Effort.core_lvs_fit(t) == True{} : Bool}:
  %Equal.sym(Nat, List.length(&2, Ef.Lv, t), 1n+m, e2) : {LawsBase.wire_fits(_) == True{} : Bool}
  hn

def ex.lvs.conv(-s: String, -s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, hn: {LawsBase.wire_fits(1n+m) == True{} : Bool},
  d: Wr.Dec<List<&2, Ef.Lv>>, tl: ex.Tl(s2, m, d)) -> ex.Lvs(s, d):
  match d:
    case Wr.Got{+t, +r}:
      (e1, e2) = tl
      +e4 = e2
      (ex.lvs.eq(s, s2, m, en, t, r, e1, e4), ex.lvs.fit(m, hn, t, e4))
    case Wr.Bad{}:
      Unit{}

def ex.lvs.nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, hn: {LawsBase.wire_fits(n) == True{} : Bool}) ->
  ex.Lvs(s, Wr.get_list.start(~Ef.Lv, ~FEf.get_lv, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, hn)
    case 1n++m:
      ex.lvs.conv(s, s2, m, en, hn, Wr.get_list.go(~Ef.Lv, ~FEf.get_lv, m, FEf.get_lv(s2)), ex.tl(m, FEf.get_lv(s2), s2, {==}))

def ex.lvs.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) ->
  ex.Lvs(s, Wr.get_list.start(~Ef.Lv, ~FEf.get_lv, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e2 = ed
      ex.lvs.nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e2), Wire.wire_nat_decoded_fits(s, n, s2, e2))
    case Wr.Bad{}:
      Unit{}

# every list of levels the decoder reads is spelled, its count fits
def ex.lvs(+s: String) -> ex.Lvs(s, FEf.get_lvs(s)):
  ex.lvs.top(s, Wr.get_nat(s), {==})

# The facts: six fields along the entry's seq
# -------------------------------------------

def ex.f2(q: FEf.P2<Bool, Bool>, r: String) -> String:
  match q:
    case FEf.P2{a, b}:
      Wr.put_bool(a, Wr.put_bool(b, r))

def ex.f3(q: FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, r: String) -> String:
  match q:
    case FEf.P2{a, b}:
      ex.f2(a, Effort.core_effort_spell_mmap(b, r))

def ex.f4(q: FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, r: String) -> String:
  match q:
    case FEf.P2{a, b}:
      ex.f3(a, Effort.core_effort_spell_mmap(b, r))

def ex.f5(q: FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, r: String) -> String:
  match q:
    case FEf.P2{a, b}:
      ex.f4(a, Effort.core_effort_spell_lvs(b, r))

def ex.f6(q: FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, List<&2, Ef.Lv>>, r: String) -> String:
  match q:
    case FEf.P2{a, b}:
      ex.f5(a, Effort.core_effort_spell_lvs(b, r))

def ex.g5(q: FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>) -> Bool:
  match q:
    case FEf.P2{a, b}:
      Effort.core_lvs_fit(b)

def ex.g6(q: FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, List<&2, Ef.Lv>>) -> Bool:
  match q:
    case FEf.P2{a, b}:
      Bool.and(ex.g5(a), Effort.core_lvs_fit(b))

def ex.F2(s: String, d: Wr.Dec<FEf.P2<Bool, Bool>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ex.f2(q, r) : String}
    case Wr.Bad{}:
      Unit

def ex.F3(s: String, d: Wr.Dec<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ex.f3(q, r) : String}
    case Wr.Bad{}:
      Unit

def ex.F4(s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ex.f4(q, r) : String}
    case Wr.Bad{}:
      Unit

def ex.F5(s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ex.f5(q, r) : String} & {ex.g5(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.F6(s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, List<&2, Ef.Lv>>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ex.f6(q, r) : String} & {ex.g6(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.ff2(-s: String, +a: Bool, -r: String, pre: {s == Wr.put_bool(a, r) : String}, e: Wr.Dec<Bool>, inv: ex.Bool(r, e)) -> ex.F2(s, FEf.seq.fin(~Bool, ~Bool, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      ex.step(z => Wr.put_bool(a, z), s, r, Wr.put_bool(b, r2), pre, inv)
    case Wr.Bad{}:
      Unit{}

def ex.fs2(-s: String, d: Wr.Dec<Bool>, inv: ex.Bool(s, d)) -> ex.F2(s, FEf.seq(~Bool, ~Bool, ~Wr.get_bool, d)):
  match d:
    case Wr.Got{+a, +r}:
      ex.ff2(s, a, r, inv, Wr.get_bool(r), ex.bool(r))
    case Wr.Bad{}:
      Unit{}

def ex.ff3(-s: String, +a: FEf.P2<Bool, Bool>, -r: String, pre: {s == ex.f2(a, r) : String}, e: Wr.Dec<Maybe<&2, Ef.LvMap>>, inv: ex.MMap(r, e)) -> ex.F3(s, FEf.seq.fin(~FEf.P2<Bool, Bool>, ~Maybe<&2, Ef.LvMap>, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      ex.step(z => ex.f2(a, z), s, r, Effort.core_effort_spell_mmap(b, r2), pre, inv)
    case Wr.Bad{}:
      Unit{}

def ex.fs3(-s: String, d: Wr.Dec<FEf.P2<Bool, Bool>>, inv: ex.F2(s, d)) -> ex.F3(s, FEf.seq(~FEf.P2<Bool, Bool>, ~Maybe<&2, Ef.LvMap>, ~FEf.get_mmap, d)):
  match d:
    case Wr.Got{+a, +r}:
      ex.ff3(s, a, r, inv, FEf.get_mmap(r), ex.mmap(r))
    case Wr.Bad{}:
      Unit{}

def ex.ff4(-s: String, +a: FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, -r: String, pre: {s == ex.f3(a, r) : String}, e: Wr.Dec<Maybe<&2, Ef.LvMap>>, inv: ex.MMap(r, e)) -> ex.F4(s, FEf.seq.fin(~FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, ~Maybe<&2, Ef.LvMap>, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      ex.step(z => ex.f3(a, z), s, r, Effort.core_effort_spell_mmap(b, r2), pre, inv)
    case Wr.Bad{}:
      Unit{}

def ex.fs4(-s: String, d: Wr.Dec<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>>, inv: ex.F3(s, d)) -> ex.F4(s, FEf.seq(~FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, ~Maybe<&2, Ef.LvMap>, ~FEf.get_mmap, d)):
  match d:
    case Wr.Got{+a, +r}:
      ex.ff4(s, a, r, inv, FEf.get_mmap(r), ex.mmap(r))
    case Wr.Bad{}:
      Unit{}

def ex.ff5(-s: String, +a: FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, -r: String, pre: {s == ex.f4(a, r) : String}, e: Wr.Dec<List<&2, Ef.Lv>>, inv: ex.Lvs(r, e)) -> ex.F5(s, FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, ~List<&2, Ef.Lv>, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      (e1, fb) = inv
      (ex.step(z => ex.f4(a, z), s, r, Effort.core_effort_spell_lvs(b, r2), pre, e1), fb)
    case Wr.Bad{}:
      Unit{}

def ex.fs5(-s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>>, inv: ex.F4(s, d)) -> ex.F5(s, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, d)):
  match d:
    case Wr.Got{+a, +r}:
      ex.ff5(s, a, r, inv, FEf.get_lvs(r), ex.lvs(r))
    case Wr.Bad{}:
      Unit{}

def ex.ff6(-s: String, +a: FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, -r: String, pre: {s == ex.f5(a, r) : String}, ga: {ex.g5(a) == True{} : Bool}, e: Wr.Dec<List<&2, Ef.Lv>>, inv: ex.Lvs(r, e)) -> ex.F6(s, FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      (e1, fb) = inv
      (ex.step(z => ex.f5(a, z), s, r, Effort.core_effort_spell_lvs(b, r2), pre, e1), LAWireSpell.ws_and_tt(ex.g5(a), Effort.core_lvs_fit(b), ga, fb))
    case Wr.Bad{}:
      Unit{}

def ex.fs6(-s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>>, inv: ex.F5(s, d)) -> ex.F6(s, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, d)):
  match d:
    case Wr.Got{+a, +r}:
      (pre, ga) = inv
      ex.ff6(s, a, r, pre, ga, FEf.get_lvs(r), ex.lvs(r))
    case Wr.Bad{}:
      Unit{}

def ex.Facts(s: String, d: Wr.Dec<FEf.Facts>) -> Type:
  match d:
    case Wr.Got{f, r}:
      {s == Effort.core_effort_spell_facts(f, r) : String} & {Effort.core_facts_fit(f) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.facts.of(-s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, List<&2, Ef.Lv>>>, inv: ex.F6(s, d)) -> ex.Facts(s, FEf.get_facts.of(d)):
  match d:
    case Wr.Got{q, r}:
      match q:
        case FEf.P2{q5, pl}:
          match q5:
            case FEf.P2{q4, re}:
              match q4:
                case FEf.P2{q3, ru}:
                  match q3:
                    case FEf.P2{q2, xp}:
                      match q2:
                        case FEf.P2{f, bm}:
                          inv
    case Wr.Bad{}:
      Unit{}

# every facts the decoder reads are spelled, their counts fit
def ex.facts(+s: String) -> ex.Facts(s, FEf.get_facts(s)):
  +d1 = Wr.get_bool(s)
  +d2 = FEf.seq(~Bool, ~Bool, ~Wr.get_bool, d1)
  +d3 = FEf.seq(~FEf.P2<Bool, Bool>, ~Maybe<&2, Ef.LvMap>, ~FEf.get_mmap, d2)
  +d4 = FEf.seq(~FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, ~Maybe<&2, Ef.LvMap>, ~FEf.get_mmap, d3)
  +d5 = FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, d4)
  +d6 = FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, d5)
  ex.facts.of(s, d6, ex.fs6(s, d5, ex.fs5(s, d4, ex.fs4(s, d3, ex.fs3(s, d2, ex.fs2(s, d1, ex.bool(s)))))))

# A request: its tag, the facts, the level, the direction
# -------------------------------------------------------

def ex.c2(q: FEf.P2<FEf.Facts, Ef.Lv>, r: String) -> String:
  match q:
    case FEf.P2{a, b}:
      Effort.core_effort_spell_facts(a, Effort.core_effort_spell_lv(b, r))

def ex.cg2(q: FEf.P2<FEf.Facts, Ef.Lv>) -> Bool:
  match q:
    case FEf.P2{a, b}:
      Effort.core_facts_fit(a)

def ex.c3(q: FEf.P2<FEf.P2<FEf.Facts, Ef.Lv>, Ef.Dir>, r: String) -> String:
  match q:
    case FEf.P2{a, b}:
      ex.c2(a, Effort.core_effort_spell_dir(b, r))

def ex.cg3(q: FEf.P2<FEf.P2<FEf.Facts, Ef.Lv>, Ef.Dir>) -> Bool:
  match q:
    case FEf.P2{a, b}:
      ex.cg2(a)

def ex.C2(s: String, d: Wr.Dec<FEf.P2<FEf.Facts, Ef.Lv>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ex.c2(q, r) : String} & {ex.cg2(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.C3(s: String, d: Wr.Dec<FEf.P2<FEf.P2<FEf.Facts, Ef.Lv>, Ef.Dir>>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ex.c3(q, r) : String} & {ex.cg3(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.cf2(-s: String, +a: FEf.Facts, -r: String, pre: {s == Effort.core_effort_spell_facts(a, r) : String}, ga: {Effort.core_facts_fit(a) == True{} : Bool}, e: Wr.Dec<Ef.Lv>, inv: ex.Lv(r, e)) -> ex.C2(s, FEf.seq.fin(~FEf.Facts, ~Ef.Lv, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      (ex.step(z => Effort.core_effort_spell_facts(a, z), s, r, Effort.core_effort_spell_lv(b, r2), pre, inv), ga)
    case Wr.Bad{}:
      Unit{}

def ex.cs2(-s: String, d: Wr.Dec<FEf.Facts>, inv: ex.Facts(s, d)) -> ex.C2(s, FEf.seq(~FEf.Facts, ~Ef.Lv, ~FEf.get_lv, d)):
  match d:
    case Wr.Got{+a, +r}:
      (pre, ga) = inv
      ex.cf2(s, a, r, pre, ga, FEf.get_lv(r), ex.lv(r))
    case Wr.Bad{}:
      Unit{}

def ex.cf3(-s: String, +a: FEf.P2<FEf.Facts, Ef.Lv>, -r: String, pre: {s == ex.c2(a, r) : String}, ga: {ex.cg2(a) == True{} : Bool}, e: Wr.Dec<Ef.Dir>, inv: ex.Dir(r, e)) -> ex.C3(s, FEf.seq.fin(~FEf.P2<FEf.Facts, Ef.Lv>, ~Ef.Dir, a, e)):
  match e:
    case Wr.Got{+b, +r2}:
      (ex.step(z => ex.c2(a, z), s, r, Effort.core_effort_spell_dir(b, r2), pre, inv), ga)
    case Wr.Bad{}:
      Unit{}

def ex.cs3(-s: String, d: Wr.Dec<FEf.P2<FEf.Facts, Ef.Lv>>, inv: ex.C2(s, d)) -> ex.C3(s, FEf.seq(~FEf.P2<FEf.Facts, Ef.Lv>, ~Ef.Dir, ~FEf.get_dir, d)):
  match d:
    case Wr.Got{+a, +r}:
      (pre, ga) = inv
      ex.cf3(s, a, r, pre, ga, FEf.get_dir(r), ex.dir(r))
    case Wr.Bad{}:
      Unit{}

# what a request decoder's answer says about its input s
def ex.Req(s: String, d: Wr.Dec<FEf.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Effort.core_effort_spell_req(q, r) : String} & {Effort.core_effort_fits(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ex.req.off(-s: String, -s0: String, en: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<FEf.Facts>, inv: ex.Facts(s0, d)) -> ex.Req(s, FEf.get_offered.of(d)):
  match d:
    case Wr.Got{+f, +r}:
      (e1, ff) = inv
      (ex.step(z => Wr.put_nat(0n, z), s, s0, Effort.core_effort_spell_facts(f, r), en, e1), ff)
    case Wr.Bad{}:
      Unit{}

def ex.req.clamp(-s: String, -s0: String, en: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<FEf.P2<FEf.Facts, Ef.Lv>>, inv: ex.C2(s0, d)) -> ex.Req(s, FEf.get_clamp.of(d)):
  match d:
    case Wr.Got{q, r}:
      match q:
        case FEf.P2{+f, +l}:
          (e1, ff) = inv
          (ex.step(z => Wr.put_nat(1n, z), s, s0, Effort.core_effort_spell_facts(f, Effort.core_effort_spell_lv(l, r)), en, e1), ff)
    case Wr.Bad{}:
      Unit{}

def ex.req.cycle(-s: String, -s0: String, en: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<FEf.P2<FEf.P2<FEf.Facts, Ef.Lv>, Ef.Dir>>, inv: ex.C3(s0, d)) -> ex.Req(s, FEf.get_cycle.of(d)):
  match d:
    case Wr.Got{q, r}:
      match q:
        case FEf.P2{q2, +x}:
          match q2:
            case FEf.P2{+f, +l}:
              (e1, ff) = inv
              (ex.step(z => Wr.put_nat(2n, z), s, s0, Effort.core_effort_spell_facts(f, Effort.core_effort_spell_lv(l, Effort.core_effort_spell_dir(x, r))), en, e1), ff)
    case Wr.Bad{}:
      Unit{}

def ex.req.tag(-s: String, t: Nat, +s0: String, en: {s == Wr.put_nat(t, s0) : String}) -> ex.Req(s, FEf.get_req.tag(t, s0)):
  match t:
    case 0n:
      ex.req.off(s, s0, en, FEf.get_facts(s0), ex.facts(s0))
    case 1n:
      +d1 = FEf.get_facts(s0)
      ex.req.clamp(s, s0, en, FEf.seq(~FEf.Facts, ~Ef.Lv, ~FEf.get_lv, d1), ex.cs2(s0, d1, ex.facts(s0)))
    case 2n:
      +d1 = FEf.get_facts(s0)
      +d2 = FEf.seq(~FEf.Facts, ~Ef.Lv, ~FEf.get_lv, d1)
      ex.req.cycle(s, s0, en, FEf.seq(~FEf.P2<FEf.Facts, Ef.Lv>, ~Ef.Dir, ~FEf.get_dir, d2), ex.cs3(s0, d2, ex.cs2(s0, d1, ex.facts(s0))))
    case 3n+k:
      Unit{}

def ex.req.go(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ex.Req(s, FEf.get_req.go(d)):
  match d:
    case Wr.Got{+t, +s0}:
      ex.req.tag(s, t, s0, Wire.wire_nat_exact(s, t, s0, ed))
    case Wr.Bad{}:
      Unit{}

# every request the decoder reads is spelled, and fits; the rest follows
def ex.req(+s: String) -> ex.Req(s, FEf.get_req(s)):
  ex.req.go(s, Wr.get_nat(s), {==})
