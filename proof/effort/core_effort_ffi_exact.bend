# eukhe: the proof of LAW core_effort_ffi_exact
# The entry's decoder reads every input as the laws' reader does, stage by
# stage (ee.*: the entry's seq chains against the laws' readers, the lists
# through ../director/list_ext.bend); the model's offer, clamp and cycle
# are the laws' (the ladder filled from the chosen map and the default
# ladders; the clamp's scan order; the wrapping step), and the entry
# spells the reply as the laws' speller does.

import Base
import ../../bend/effort.bend as Ef
import ../../bend/ffi_effort.bend as FEf
import ../../bend/infer.bend as If
import ../../bend/wire.bend as Wr
import ../../laws/effort/entry.bend as EffortEntry
import ../director/list_ext.bend as LX

# Reading: the single fields
# --------------------------

def ee.lv_tag(t: Nat, -s: String) -> {FEf.get_lv.tag(t, s) == EffortEntry.er.lv.tag(t, s) : Wr.Dec<Ef.Lv>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n+p:
      {==}

def ee.lv_go(r: Wr.Dec<Nat>) -> {FEf.get_lv.go(r) == EffortEntry.er.lv.go(r) : Wr.Dec<Ef.Lv>}:
  match r:
    case Wr.Got{t, s}:
      ee.lv_tag(t, s)
    case Wr.Bad{}:
      {==}

def ee.lv(s: String) -> {FEf.get_lv(s) == EffortEntry.er.lv(s) : Wr.Dec<Ef.Lv>}:
  ee.lv_go(Wr.get_nat(s))

def ee.ent_tag(t: Nat, -s: String) -> {FEf.get_ent.tag(t, s) == EffortEntry.er.ent.tag(t, s) : Wr.Dec<Ef.Ent>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n+p:
      {==}

def ee.ent_go(r: Wr.Dec<Nat>) -> {FEf.get_ent.go(r) == EffortEntry.er.ent(r) : Wr.Dec<Ef.Ent>}:
  match r:
    case Wr.Got{t, s}:
      ee.ent_tag(t, s)
    case Wr.Bad{}:
      {==}

def ee.dir_tag(t: Nat, -s: String) -> {FEf.get_dir.tag(t, s) == EffortEntry.er.dir.tag(t, s) : Wr.Dec<Ef.Dir>}:
  match t:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n+p:
      {==}

def ee.dir_go(r: Wr.Dec<Nat>) -> {FEf.get_dir.go(r) == EffortEntry.er.dir(r) : Wr.Dec<Ef.Dir>}:
  match r:
    case Wr.Got{t, s}:
      ee.dir_tag(t, s)
    case Wr.Bad{}:
      {==}

def ee.lvs(+s: String) -> {FEf.get_lvs(s) == EffortEntry.er.lvs(s) : Wr.Dec<List<&2, Ef.Lv>>}:
  LX.lx.get(~Ef.Lv, ~FEf.get_lv, ~EffortEntry.er.lv, ~ee.lv, s)

# Reading: the records
# --------------------

def ee.map7(+o: Ef.Ent, +mi: Ef.Ent, +lo: Ef.Ent, +me: Ef.Ent, +hi: Ef.Ent, +xh: Ef.Ent, d: Wr.Dec<Ef.Ent>) -> {FEf.get_map.of(FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, FEf.P2{FEf.P2{FEf.P2{FEf.P2{FEf.P2{o, mi}, lo}, me}, hi}, xh}, d)) == EffortEntry.er.map.mx(o, mi, lo, me, hi, xh, d) : Wr.Dec<Ef.LvMap>}:
  match d:
    case Wr.Got{mx, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ee.map6(+o: Ef.Ent, +mi: Ef.Ent, +lo: Ef.Ent, +me: Ef.Ent, +hi: Ef.Ent, d: Wr.Dec<Ef.Ent>) -> {FEf.get_map.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, FEf.P2{FEf.P2{FEf.P2{FEf.P2{o, mi}, lo}, me}, hi}, d))) == EffortEntry.er.map.xh(o, mi, lo, me, hi, d) : Wr.Dec<Ef.LvMap>}:
  match d:
    case Wr.Got{+xh, +s}:
      %ee.ent_go(Wr.get_nat(s)) : {FEf.get_map.of(FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, FEf.P2{FEf.P2{FEf.P2{FEf.P2{FEf.P2{o, mi}, lo}, me}, hi}, xh}, FEf.get_ent(s))) == EffortEntry.er.map.mx(o, mi, lo, me, hi, xh, _) : Wr.Dec<Ef.LvMap>}
      ee.map7(o, mi, lo, me, hi, xh, FEf.get_ent(s))
    case Wr.Bad{}:
      {==}

def ee.map5(+o: Ef.Ent, +mi: Ef.Ent, +lo: Ef.Ent, +me: Ef.Ent, d: Wr.Dec<Ef.Ent>) -> {FEf.get_map.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, FEf.P2{FEf.P2{FEf.P2{o, mi}, lo}, me}, d)))) == EffortEntry.er.map.hi(o, mi, lo, me, d) : Wr.Dec<Ef.LvMap>}:
  match d:
    case Wr.Got{+hi, +s}:
      %ee.ent_go(Wr.get_nat(s)) : {FEf.get_map.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, FEf.P2{FEf.P2{FEf.P2{FEf.P2{o, mi}, lo}, me}, hi}, FEf.get_ent(s)))) == EffortEntry.er.map.xh(o, mi, lo, me, hi, _) : Wr.Dec<Ef.LvMap>}
      ee.map6(o, mi, lo, me, hi, FEf.get_ent(s))
    case Wr.Bad{}:
      {==}

def ee.map4(+o: Ef.Ent, +mi: Ef.Ent, +lo: Ef.Ent, d: Wr.Dec<Ef.Ent>) -> {FEf.get_map.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq.fin(~FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, ~Ef.Ent, FEf.P2{FEf.P2{o, mi}, lo}, d))))) == EffortEntry.er.map.me(o, mi, lo, d) : Wr.Dec<Ef.LvMap>}:
  match d:
    case Wr.Got{+me, +s}:
      %ee.ent_go(Wr.get_nat(s)) : {FEf.get_map.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, FEf.P2{FEf.P2{FEf.P2{o, mi}, lo}, me}, FEf.get_ent(s))))) == EffortEntry.er.map.hi(o, mi, lo, me, _) : Wr.Dec<Ef.LvMap>}
      ee.map5(o, mi, lo, me, FEf.get_ent(s))
    case Wr.Bad{}:
      {==}

def ee.map3(+o: Ef.Ent, +mi: Ef.Ent, d: Wr.Dec<Ef.Ent>) -> {FEf.get_map.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq.fin(~FEf.P2<Ef.Ent, Ef.Ent>, ~Ef.Ent, FEf.P2{o, mi}, d)))))) == EffortEntry.er.map.lo(o, mi, d) : Wr.Dec<Ef.LvMap>}:
  match d:
    case Wr.Got{+lo, +s}:
      %ee.ent_go(Wr.get_nat(s)) : {FEf.get_map.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq.fin(~FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, ~Ef.Ent, FEf.P2{FEf.P2{o, mi}, lo}, FEf.get_ent(s)))))) == EffortEntry.er.map.me(o, mi, lo, _) : Wr.Dec<Ef.LvMap>}
      ee.map4(o, mi, lo, FEf.get_ent(s))
    case Wr.Bad{}:
      {==}

def ee.map2(+o: Ef.Ent, d: Wr.Dec<Ef.Ent>) -> {FEf.get_map.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<Ef.Ent, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq.fin(~Ef.Ent, ~Ef.Ent, o, d))))))) == EffortEntry.er.map.mi(o, d) : Wr.Dec<Ef.LvMap>}:
  match d:
    case Wr.Got{+mi, +s}:
      %ee.ent_go(Wr.get_nat(s)) : {FEf.get_map.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq.fin(~FEf.P2<Ef.Ent, Ef.Ent>, ~Ef.Ent, FEf.P2{o, mi}, FEf.get_ent(s))))))) == EffortEntry.er.map.lo(o, mi, _) : Wr.Dec<Ef.LvMap>}
      ee.map3(o, mi, FEf.get_ent(s))
    case Wr.Bad{}:
      {==}

def ee.map1(d: Wr.Dec<Ef.Ent>) -> {FEf.get_map.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<Ef.Ent, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~Ef.Ent, ~Ef.Ent, ~FEf.get_ent, d))))))) == EffortEntry.er.map.o(d) : Wr.Dec<Ef.LvMap>}:
  match d:
    case Wr.Got{+o, +s}:
      %ee.ent_go(Wr.get_nat(s)) : {FEf.get_map.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<FEf.P2<Ef.Ent, Ef.Ent>, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq(~FEf.P2<Ef.Ent, Ef.Ent>, ~Ef.Ent, ~FEf.get_ent, FEf.seq.fin(~Ef.Ent, ~Ef.Ent, o, FEf.get_ent(s)))))))) == EffortEntry.er.map.mi(o, _) : Wr.Dec<Ef.LvMap>}
      ee.map2(o, FEf.get_ent(s))
    case Wr.Bad{}:
      {==}

def ee.map(+s: String) -> {FEf.get_map(s) == EffortEntry.er.map(s) : Wr.Dec<Ef.LvMap>}:
  %ee.ent_go(Wr.get_nat(s)) : {FEf.get_map(s) == EffortEntry.er.map.o(_) : Wr.Dec<Ef.LvMap>}
  ee.map1(FEf.get_ent(s))

def ee.mmap_some(r: Wr.Dec<Ef.LvMap>) -> {FEf.get_mmap.some(r) == EffortEntry.er.mmap.some(r) : Wr.Dec<Maybe<&2, Ef.LvMap>>}:
  match r:
    case Wr.Got{m, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ee.mmap_tag(t: Nat, +s: String) -> {FEf.get_mmap.tag(t, s) == EffortEntry.er.mmap.tag(t, s) : Wr.Dec<Maybe<&2, Ef.LvMap>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      %ee.map(s) : {FEf.get_mmap.some(FEf.get_map(s)) == EffortEntry.er.mmap.some(_) : Wr.Dec<Maybe<&2, Ef.LvMap>>}
      ee.mmap_some(FEf.get_map(s))
    case 2n+p:
      {==}

def ee.mmap_go(r: Wr.Dec<Nat>) -> {FEf.get_mmap.go(r) == EffortEntry.er.mmap(r) : Wr.Dec<Maybe<&2, Ef.LvMap>>}:
  match r:
    case Wr.Got{t, +s}:
      ee.mmap_tag(t, s)
    case Wr.Bad{}:
      {==}

def ee.facts6(+f: Bool, +bm: Bool, +ex: Maybe<&2, Ef.LvMap>, +ru: Maybe<&2, Ef.LvMap>, +re: List<&2, Ef.Lv>, d: Wr.Dec<List<&2, Ef.Lv>>) -> {FEf.get_facts.of(FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, FEf.P2{FEf.P2{FEf.P2{FEf.P2{f, bm}, ex}, ru}, re}, d)) == EffortEntry.er.facts.pl(f, bm, ex, ru, re, d) : Wr.Dec<FEf.Facts>}:
  match d:
    case Wr.Got{pl, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ee.facts5(+f: Bool, +bm: Bool, +ex: Maybe<&2, Ef.LvMap>, +ru: Maybe<&2, Ef.LvMap>, d: Wr.Dec<List<&2, Ef.Lv>>) -> {FEf.get_facts.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, ~List<&2, Ef.Lv>, FEf.P2{FEf.P2{FEf.P2{f, bm}, ex}, ru}, d))) == EffortEntry.er.facts.re(f, bm, ex, ru, d) : Wr.Dec<FEf.Facts>}:
  match d:
    case Wr.Got{+re, +s}:
      %ee.lvs(s) : {FEf.get_facts.of(FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, FEf.P2{FEf.P2{FEf.P2{FEf.P2{f, bm}, ex}, ru}, re}, FEf.get_lvs(s))) == EffortEntry.er.facts.pl(f, bm, ex, ru, re, _) : Wr.Dec<FEf.Facts>}
      ee.facts6(f, bm, ex, ru, re, FEf.get_lvs(s))
    case Wr.Bad{}:
      {==}

def ee.facts4(+f: Bool, +bm: Bool, +ex: Maybe<&2, Ef.LvMap>, d: Wr.Dec<Maybe<&2, Ef.LvMap>>) -> {FEf.get_facts.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.seq.fin(~FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, ~Maybe<&2, Ef.LvMap>, FEf.P2{FEf.P2{f, bm}, ex}, d)))) == EffortEntry.er.facts.ru(f, bm, ex, d) : Wr.Dec<FEf.Facts>}:
  match d:
    case Wr.Got{+ru, +s}:
      %ee.lvs(s) : {FEf.get_facts.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.seq.fin(~FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, ~List<&2, Ef.Lv>, FEf.P2{FEf.P2{FEf.P2{f, bm}, ex}, ru}, FEf.get_lvs(s)))) == EffortEntry.er.facts.re(f, bm, ex, ru, _) : Wr.Dec<FEf.Facts>}
      ee.facts5(f, bm, ex, ru, FEf.get_lvs(s))
    case Wr.Bad{}:
      {==}

def ee.facts3(+f: Bool, +bm: Bool, d: Wr.Dec<Maybe<&2, Ef.LvMap>>) -> {FEf.get_facts.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.seq(~FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, ~Maybe<&2, Ef.LvMap>, ~FEf.get_mmap, FEf.seq.fin(~FEf.P2<Bool, Bool>, ~Maybe<&2, Ef.LvMap>, FEf.P2{f, bm}, d))))) == EffortEntry.er.facts.ex(f, bm, d) : Wr.Dec<FEf.Facts>}:
  match d:
    case Wr.Got{+ex, +s}:
      %ee.mmap_go(Wr.get_nat(s)) : {FEf.get_facts.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.seq.fin(~FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, ~Maybe<&2, Ef.LvMap>, FEf.P2{FEf.P2{f, bm}, ex}, FEf.get_mmap(s))))) == EffortEntry.er.facts.ru(f, bm, ex, _) : Wr.Dec<FEf.Facts>}
      ee.facts4(f, bm, ex, FEf.get_mmap(s))
    case Wr.Bad{}:
      {==}

def ee.facts2(+f: Bool, d: Wr.Dec<Bool>) -> {FEf.get_facts.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.seq(~FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, ~Maybe<&2, Ef.LvMap>, ~FEf.get_mmap, FEf.seq(~FEf.P2<Bool, Bool>, ~Maybe<&2, Ef.LvMap>, ~FEf.get_mmap, FEf.seq.fin(~Bool, ~Bool, f, d)))))) == EffortEntry.er.facts.bm(f, d) : Wr.Dec<FEf.Facts>}:
  match d:
    case Wr.Got{+bm, +s}:
      %ee.mmap_go(Wr.get_nat(s)) : {FEf.get_facts.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.seq(~FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, ~Maybe<&2, Ef.LvMap>, ~FEf.get_mmap, FEf.seq.fin(~FEf.P2<Bool, Bool>, ~Maybe<&2, Ef.LvMap>, FEf.P2{f, bm}, FEf.get_mmap(s)))))) == EffortEntry.er.facts.ex(f, bm, _) : Wr.Dec<FEf.Facts>}
      ee.facts3(f, bm, FEf.get_mmap(s))
    case Wr.Bad{}:
      {==}

def ee.facts1(d: Wr.Dec<Bool>) -> {FEf.get_facts.of(FEf.seq(~FEf.P2<FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, List<&2, Ef.Lv>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.seq(~FEf.P2<FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, Maybe<&2, Ef.LvMap>>, ~List<&2, Ef.Lv>, ~FEf.get_lvs, FEf.seq(~FEf.P2<FEf.P2<Bool, Bool>, Maybe<&2, Ef.LvMap>>, ~Maybe<&2, Ef.LvMap>, ~FEf.get_mmap, FEf.seq(~FEf.P2<Bool, Bool>, ~Maybe<&2, Ef.LvMap>, ~FEf.get_mmap, FEf.seq(~Bool, ~Bool, ~Wr.get_bool, d)))))) == EffortEntry.er.facts.f(d) : Wr.Dec<FEf.Facts>}:
  match d:
    case Wr.Got{+f, +s}:
      ee.facts2(f, Wr.get_bool(s))
    case Wr.Bad{}:
      {==}

def ee.facts(+s: String) -> {FEf.get_facts(s) == EffortEntry.er.facts(s) : Wr.Dec<FEf.Facts>}:
  ee.facts1(Wr.get_bool(s))

def ee.offered_of(r: Wr.Dec<FEf.Facts>) -> {FEf.get_offered.of(r) == EffortEntry.er.offered(r) : Wr.Dec<FEf.Req>}:
  match r:
    case Wr.Got{f, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ee.clamp2(+f: FEf.Facts, d: Wr.Dec<Ef.Lv>) -> {FEf.get_clamp.of(FEf.seq.fin(~FEf.Facts, ~Ef.Lv, f, d)) == EffortEntry.er.clamp.l(f, d) : Wr.Dec<FEf.Req>}:
  match d:
    case Wr.Got{l, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ee.clamp1(d: Wr.Dec<FEf.Facts>) -> {FEf.get_clamp.of(FEf.seq(~FEf.Facts, ~Ef.Lv, ~FEf.get_lv, d)) == EffortEntry.er.clamp(d) : Wr.Dec<FEf.Req>}:
  match d:
    case Wr.Got{+f, +s}:
      %ee.lv(s) : {FEf.get_clamp.of(FEf.seq.fin(~FEf.Facts, ~Ef.Lv, f, FEf.get_lv(s))) == EffortEntry.er.clamp.l(f, _) : Wr.Dec<FEf.Req>}
      ee.clamp2(f, FEf.get_lv(s))
    case Wr.Bad{}:
      {==}

def ee.cycle3(+f: FEf.Facts, +l: Ef.Lv, d: Wr.Dec<Ef.Dir>) -> {FEf.get_cycle.of(FEf.seq.fin(~FEf.P2<FEf.Facts, Ef.Lv>, ~Ef.Dir, FEf.P2{f, l}, d)) == EffortEntry.er.cycle.d(f, l, d) : Wr.Dec<FEf.Req>}:
  match d:
    case Wr.Got{d, s}:
      {==}
    case Wr.Bad{}:
      {==}

def ee.cycle2(+f: FEf.Facts, d: Wr.Dec<Ef.Lv>) -> {FEf.get_cycle.of(FEf.seq(~FEf.P2<FEf.Facts, Ef.Lv>, ~Ef.Dir, ~FEf.get_dir, FEf.seq.fin(~FEf.Facts, ~Ef.Lv, f, d))) == EffortEntry.er.cycle.l(f, d) : Wr.Dec<FEf.Req>}:
  match d:
    case Wr.Got{+l, +s}:
      %ee.dir_go(Wr.get_nat(s)) : {FEf.get_cycle.of(FEf.seq.fin(~FEf.P2<FEf.Facts, Ef.Lv>, ~Ef.Dir, FEf.P2{f, l}, FEf.get_dir(s))) == EffortEntry.er.cycle.d(f, l, _) : Wr.Dec<FEf.Req>}
      ee.cycle3(f, l, FEf.get_dir(s))
    case Wr.Bad{}:
      {==}

def ee.cycle1(d: Wr.Dec<FEf.Facts>) -> {FEf.get_cycle.of(FEf.seq(~FEf.P2<FEf.Facts, Ef.Lv>, ~Ef.Dir, ~FEf.get_dir, FEf.seq(~FEf.Facts, ~Ef.Lv, ~FEf.get_lv, d))) == EffortEntry.er.cycle(d) : Wr.Dec<FEf.Req>}:
  match d:
    case Wr.Got{+f, +s}:
      %ee.lv(s) : {FEf.get_cycle.of(FEf.seq(~FEf.P2<FEf.Facts, Ef.Lv>, ~Ef.Dir, ~FEf.get_dir, FEf.seq.fin(~FEf.Facts, ~Ef.Lv, f, FEf.get_lv(s)))) == EffortEntry.er.cycle.l(f, _) : Wr.Dec<FEf.Req>}
      ee.cycle2(f, FEf.get_lv(s))
    case Wr.Bad{}:
      {==}

def ee.req_tag(t: Nat, +s: String) -> {FEf.get_req.tag(t, s) == EffortEntry.er.req.tag(t, s) : Wr.Dec<FEf.Req>}:
  match t:
    case 0n:
      %ee.facts(s) : {FEf.get_req.tag(0n, s) == EffortEntry.er.offered(_) : Wr.Dec<FEf.Req>}
      ee.offered_of(FEf.get_facts(s))
    case 1n:
      %ee.facts(s) : {FEf.get_req.tag(1n, s) == EffortEntry.er.clamp(_) : Wr.Dec<FEf.Req>}
      ee.clamp1(FEf.get_facts(s))
    case 2n:
      %ee.facts(s) : {FEf.get_req.tag(2n, s) == EffortEntry.er.cycle(_) : Wr.Dec<FEf.Req>}
      ee.cycle1(FEf.get_facts(s))
    case 3n+p:
      {==}

def ee.req(r: Wr.Dec<Nat>) -> {FEf.get_req.go(r) == EffortEntry.er.req(r) : Wr.Dec<FEf.Req>}:
  match r:
    case Wr.Got{t, +s}:
      ee.req_tag(t, s)
    case Wr.Bad{}:
      {==}

# The ladder
# ----------

def ee.idx(l: Ef.Lv) -> {Ef.Lv.idx(l) == EffortEntry.es.idx(l) : Nat}:
  match l:
    case Ef.Off{}:
      {==}
    case Ef.Minimal{}:
      {==}
    case Ef.Low{}:
      {==}
    case Ef.Medium{}:
      {==}
    case Ef.High{}:
      {==}
    case Ef.Xhigh{}:
      {==}
    case Ef.Max{}:
      {==}

def ee.eq(+a: Ef.Lv, +b: Ef.Lv) -> {Ef.Lv.eq(a, b) == EffortEntry.es.same(a, b) : Bool}:
  %ee.idx(a) : {Ef.Lv.eq(a, b) == Nat.is_eq(_, EffortEntry.es.idx(b)) : Bool}
  %ee.idx(b) : {Ef.Lv.eq(a, b) == Nat.is_eq(Ef.Lv.idx(a), _) : Bool}
  {==}

def ee.has(xs: List<&2, Ef.Lv>, +l: Ef.Lv) -> {Ef.has(xs, l) == EffortEntry.es.has(xs, l) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %ee.has(rest, l) : {Ef.has(x <> rest, l) == Bool.or(EffortEntry.es.same(x, l), _) : Bool}
      %ee.eq(x, l) : {Ef.has(x <> rest, l) == Bool.or(_, Ef.has(rest, l)) : Bool}
      {==}

def ee.wire(e: Ef.Ent) -> {If.lad.wired.e(e) == EffortEntry.es.wire(e) : Bool}:
  match e:
    case Ef.Missing{}:
      {==}
    case Ef.Null{}:
      {==}
    case Ef.Wire{}:
      {==}

def ee.reasons(flag: Bool, bm: Bool, ex: Maybe<&2, Ef.LvMap>) -> {If.lad.reasons(flag, bm, ex) == EffortEntry.es.reasons(flag, bm, ex) : Bool}:
  match flag:
    case True{}:
      {==}
    case False{}:
      match bm:
        case True{}:
          match ex:
            case None{}:
              {==}
            case Some{m}:
              match m:
                case Ef.LvMap{+o, +mi, +lo, +me, +hi, +xh, +mx}:
                  %ee.wire(o) : {Bool.or(If.lad.wired.e(o), Bool.or(If.lad.wired.e(mi), Bool.or(If.lad.wired.e(lo), Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))))))) == Bool.or(_, Bool.or(EffortEntry.es.wire(mi), Bool.or(EffortEntry.es.wire(lo), Bool.or(EffortEntry.es.wire(me), Bool.or(EffortEntry.es.wire(hi), Bool.or(EffortEntry.es.wire(xh), EffortEntry.es.wire(mx))))))) : Bool}
                  %ee.wire(mi) : {Bool.or(If.lad.wired.e(o), Bool.or(If.lad.wired.e(mi), Bool.or(If.lad.wired.e(lo), Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))))))) == Bool.or(If.lad.wired.e(o), Bool.or(_, Bool.or(EffortEntry.es.wire(lo), Bool.or(EffortEntry.es.wire(me), Bool.or(EffortEntry.es.wire(hi), Bool.or(EffortEntry.es.wire(xh), EffortEntry.es.wire(mx))))))) : Bool}
                  %ee.wire(lo) : {Bool.or(If.lad.wired.e(o), Bool.or(If.lad.wired.e(mi), Bool.or(If.lad.wired.e(lo), Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))))))) == Bool.or(If.lad.wired.e(o), Bool.or(If.lad.wired.e(mi), Bool.or(_, Bool.or(EffortEntry.es.wire(me), Bool.or(EffortEntry.es.wire(hi), Bool.or(EffortEntry.es.wire(xh), EffortEntry.es.wire(mx))))))) : Bool}
                  %ee.wire(me) : {Bool.or(If.lad.wired.e(o), Bool.or(If.lad.wired.e(mi), Bool.or(If.lad.wired.e(lo), Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))))))) == Bool.or(If.lad.wired.e(o), Bool.or(If.lad.wired.e(mi), Bool.or(If.lad.wired.e(lo), Bool.or(_, Bool.or(EffortEntry.es.wire(hi), Bool.or(EffortEntry.es.wire(xh), EffortEntry.es.wire(mx))))))) : Bool}
                  %ee.wire(hi) : {Bool.or(If.lad.wired.e(o), Bool.or(If.lad.wired.e(mi), Bool.or(If.lad.wired.e(lo), Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))))))) == Bool.or(If.lad.wired.e(o), Bool.or(If.lad.wired.e(mi), Bool.or(If.lad.wired.e(lo), Bool.or(If.lad.wired.e(me), Bool.or(_, Bool.or(EffortEntry.es.wire(xh), EffortEntry.es.wire(mx))))))) : Bool}
                  %ee.wire(xh) : {Bool.or(If.lad.wired.e(o), Bool.or(If.lad.wired.e(mi), Bool.or(If.lad.wired.e(lo), Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))))))) == Bool.or(If.lad.wired.e(o), Bool.or(If.lad.wired.e(mi), Bool.or(If.lad.wired.e(lo), Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(_, EffortEntry.es.wire(mx))))))) : Bool}
                  %ee.wire(mx) : {Bool.or(If.lad.wired.e(o), Bool.or(If.lad.wired.e(mi), Bool.or(If.lad.wired.e(lo), Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), If.lad.wired.e(mx))))))) == Bool.or(If.lad.wired.e(o), Bool.or(If.lad.wired.e(mi), Bool.or(If.lad.wired.e(lo), Bool.or(If.lad.wired.e(me), Bool.or(If.lad.wired.e(hi), Bool.or(If.lad.wired.e(xh), _)))))) : Bool}
                  {==}
        case False{}:
          {==}

def ee.chosen(ex: Maybe<&2, Ef.LvMap>, ru: Maybe<&2, Ef.LvMap>) -> {If.lad.chosen(ex, ru) == EffortEntry.es.chosen(ex, ru) : Ef.LvMap}:
  match ex:
    case Some{e}:
      {==}
    case None{}:
      match ru:
        case Some{r}:
          {==}
        case None{}:
          {==}

def ee.keep_ent(+l: Ef.Lv, b: Bool) -> {Ef.keep.e(l, If.lad.ent(b)) == b : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ee.keep_fill(+l: Ef.Lv, e: Ef.Ent, +rs: List<&2, Ef.Lv>) -> {Ef.keep.e(l, If.lad.fill.e(l, e, rs)) == EffortEntry.es.keep.e(e, rs, l) : Bool}:
  match e:
    case Ef.Missing{}:
      %ee.has(rs, l) : {Ef.keep.e(l, If.lad.ent(Ef.has(rs, l))) == _ : Bool}
      ee.keep_ent(l, Ef.has(rs, l))
    case Ef.Null{}:
      {==}
    case Ef.Wire{}:
      {==}

def ee.keep(r: Bool, ch: Ef.LvMap, +rs: List<&2, Ef.Lv>, +pl: List<&2, Ef.Lv>, l: Ef.Lv) -> {Ef.keep(If.lad.map(r, ch, If.Defaults{rs, pl}), l) == EffortEntry.es.keep(r, ch, rs, pl, l) : Bool}:
  match r:
    case True{}:
      match ch:
        case Ef.LvMap{o, mi, lo, me, hi, xh, mx}:
          match l:
            case Ef.Off{}:
              ee.keep_fill(Ef.Off{}, o, rs)
            case Ef.Minimal{}:
              ee.keep_fill(Ef.Minimal{}, mi, rs)
            case Ef.Low{}:
              ee.keep_fill(Ef.Low{}, lo, rs)
            case Ef.Medium{}:
              ee.keep_fill(Ef.Medium{}, me, rs)
            case Ef.High{}:
              ee.keep_fill(Ef.High{}, hi, rs)
            case Ef.Xhigh{}:
              ee.keep_fill(Ef.Xhigh{}, xh, rs)
            case Ef.Max{}:
              ee.keep_fill(Ef.Max{}, mx, rs)
    case False{}:
      match l:
        case Ef.Off{}:
          ee.keep_fill(Ef.Off{}, Ef.Missing{}, pl)
        case Ef.Minimal{}:
          ee.keep_fill(Ef.Minimal{}, Ef.Missing{}, pl)
        case Ef.Low{}:
          ee.keep_fill(Ef.Low{}, Ef.Missing{}, pl)
        case Ef.Medium{}:
          ee.keep_fill(Ef.Medium{}, Ef.Missing{}, pl)
        case Ef.High{}:
          ee.keep_fill(Ef.High{}, Ef.Missing{}, pl)
        case Ef.Xhigh{}:
          ee.keep_fill(Ef.Xhigh{}, Ef.Missing{}, pl)
        case Ef.Max{}:
          ee.keep_fill(Ef.Max{}, Ef.Missing{}, pl)

def ee.cons_if(b: Bool, x: Ef.Lv, xs: List<&2, Ef.Lv>) -> {Ef.cons_if(b, x, xs) == EffortEntry.es.if(List<&2, Ef.Lv>, b, x <> xs, xs) : List<&2, Ef.Lv>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ee.offer(xs: List<&2, Ef.Lv>, +r: Bool, +ch: Ef.LvMap, +rs: List<&2, Ef.Lv>, +pl: List<&2, Ef.Lv>) -> {Ef.offer(If.lad.map(r, ch, If.Defaults{rs, pl}), xs) == EffortEntry.es.offer(xs, r, ch, rs, pl) : List<&2, Ef.Lv>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +M = If.lad.map(r, ch, If.Defaults{rs, pl})
      %ee.offer(rest, r, ch, rs, pl) : {Ef.offer(M, x <> rest) == EffortEntry.es.if(List<&2, Ef.Lv>, EffortEntry.es.keep(r, ch, rs, pl, x), x <> _, _) : List<&2, Ef.Lv>}
      %ee.keep(r, ch, rs, pl, x) : {Ef.offer(M, x <> rest) == EffortEntry.es.if(List<&2, Ef.Lv>, _, x <> Ef.offer(M, rest), Ef.offer(M, rest)) : List<&2, Ef.Lv>}
      ee.cons_if(Ef.keep(M, x), x, Ef.offer(M, rest))

def ee.offered(f: FEf.Facts) -> {Ef.offered(FEf.model(f)) == EffortEntry.es.offered(f) : List<&2, Ef.Lv>}:
  match f:
    case FEf.Facts{+flag, +bm, +ex, +ru, +rs, +pl}:
      %ee.reasons(flag, bm, ex) : {Ef.offered(FEf.model(FEf.Facts{flag, bm, ex, ru, rs, pl})) == EffortEntry.es.offer(EffortEntry.es.ladder(), _, EffortEntry.es.chosen(ex, ru), rs, pl) : List<&2, Ef.Lv>}
      %ee.chosen(ex, ru) : {Ef.offered(FEf.model(FEf.Facts{flag, bm, ex, ru, rs, pl})) == EffortEntry.es.offer(EffortEntry.es.ladder(), If.lad.reasons(flag, bm, ex), _, rs, pl) : List<&2, Ef.Lv>}
      ee.offer(EffortEntry.es.ladder(), If.lad.reasons(flag, bm, ex), If.lad.chosen(ex, ru), rs, pl)

# The clamp
# ---------

def ee.first(xs: List<&2, Ef.Lv>, d: Ef.Lv) -> {Ef.first(xs, d) == EffortEntry.es.first(xs, d) : Ef.Lv}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

def ee.pick_step(b: Bool, +x: Ef.Lv, +rest: List<&2, Ef.Lv>, +lad: List<&2, Ef.Lv>, +d: Ef.Lv, ih: {Ef.find.go(rest, lad, d, Ef.in.at(rest, lad)) == EffortEntry.es.or(EffortEntry.es.pick(lad, rest), d) : Ef.Lv}) -> {Ef.find.go(x <> rest, lad, d, b) == EffortEntry.es.or(EffortEntry.es.if(Maybe<&2, Ef.Lv>, b, Some{x}, EffortEntry.es.pick(lad, rest)), d) : Ef.Lv}:
  match b:
    case True{}:
      {==}
    case False{}:
      ih

# the scan from xs finds the first level of xs that lad lists, else d
def ee.pick(xs: List<&2, Ef.Lv>, +lad: List<&2, Ef.Lv>, +d: Ef.Lv) -> {Ef.find.go(xs, lad, d, Ef.in.at(xs, lad)) == EffortEntry.es.or(EffortEntry.es.pick(lad, xs), d) : Ef.Lv}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %ee.has(lad, x) : {Ef.find.go(x <> rest, lad, d, Ef.has(lad, x)) == EffortEntry.es.or(EffortEntry.es.if(Maybe<&2, Ef.Lv>, _, Some{x}, EffortEntry.es.pick(lad, rest)), d) : Ef.Lv}
      ee.pick_step(Ef.has(lad, x), x, rest, lad, d, ee.pick(rest, lad, d))

def ee.scan(l: Ef.Lv) -> {Ef.scan(l) == l <> EffortEntry.es.others(l) : List<&2, Ef.Lv>}:
  match l:
    case Ef.Off{}:
      {==}
    case Ef.Minimal{}:
      {==}
    case Ef.Low{}:
      {==}
    case Ef.Medium{}:
      {==}
    case Ef.High{}:
      {==}
    case Ef.Xhigh{}:
      {==}
    case Ef.Max{}:
      {==}

# a level lad does not list is skipped
def ee.skip(+x: Ef.Lv, +rest: List<&2, Ef.Lv>, +lad: List<&2, Ef.Lv>, +d: Ef.Lv, e: {Ef.has(lad, x) == False{} : Bool}) -> {Ef.find.go(x <> rest, lad, d, Ef.has(lad, x)) == Ef.find.go(rest, lad, d, Ef.in.at(rest, lad)) : Ef.Lv}:
  %Equal.sym(Bool, Ef.has(lad, x), False{}, e) : {Ef.find.go(x <> rest, lad, d, _) == Ef.find.go(rest, lad, d, Ef.in.at(rest, lad)) : Ef.Lv}
  {==}

def ee.clamp_at(+lad: List<&2, Ef.Lv>, +l: Ef.Lv, b: Bool, e: {Ef.has(lad, l) == b : Bool}) -> {Ef.clamp.at(b, l, lad) == EffortEntry.es.if(Ef.Lv, b, l, EffortEntry.es.or(EffortEntry.es.pick(lad, EffortEntry.es.others(l)), EffortEntry.es.first(lad, Ef.Off{}))) : Ef.Lv}:
  match b:
    case True{}:
      {==}
    case False{}:
      +O = EffortEntry.es.others(l)
      +D = Ef.first(lad, Ef.Off{})
      %Equal.sym(List<&2, Ef.Lv>, Ef.scan(l), l <> O, ee.scan(l)) : {Ef.find.go(_, lad, D, Ef.in.at(_, lad)) == EffortEntry.es.or(EffortEntry.es.pick(lad, O), EffortEntry.es.first(lad, Ef.Off{})) : Ef.Lv}
      %ee.first(lad, Ef.Off{}) : {Ef.find.go(l <> O, lad, D, Ef.has(lad, l)) == EffortEntry.es.or(EffortEntry.es.pick(lad, O), _) : Ef.Lv}
      Equal.trans(Ef.Lv, Ef.find.go(l <> O, lad, D, Ef.has(lad, l)), Ef.find.go(O, lad, D, Ef.in.at(O, lad)), EffortEntry.es.or(EffortEntry.es.pick(lad, O), D), ee.skip(l, O, lad, D, e), ee.pick(O, lad, D))

def ee.clamp(+lad: List<&2, Ef.Lv>, +l: Ef.Lv) -> {Ef.clamp.in(lad, l) == EffortEntry.es.clamp(lad, l) : Ef.Lv}:
  %ee.has(lad, l) : {Ef.clamp.in(lad, l) == EffortEntry.es.if(Ef.Lv, _, l, EffortEntry.es.or(EffortEntry.es.pick(lad, EffortEntry.es.others(l)), EffortEntry.es.first(lad, Ef.Off{}))) : Ef.Lv}
  ee.clamp_at(lad, l, Ef.has(lad, l), {==})

# The cycle
# ---------

def ee.two(xs: List<&2, Ef.Lv>) -> {Ef.two(xs) == EffortEntry.es.two(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match rest:
        case Nil{}:
          {==}
        case y <> more:
          {==}

def ee.last(xs: List<&2, Ef.Lv>, d: Ef.Lv) -> {Ef.last(xs, d) == EffortEntry.es.last(xs, d) : Ef.Lv}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      ee.last(rest, x)

def ee.fwd_step(b: Bool, -x: Ef.Lv, +rest: List<&2, Ef.Lv>, +c: Ef.Lv, +top: Ef.Lv) -> {Ef.fwd.go(x <> rest, c, top, b) == EffortEntry.es.if(Maybe<&2, Ef.Lv>, b, Some{Ef.first(rest, top)}, Ef.fwd.go(rest, c, top, Ef.at(rest, c))) : Maybe<&2, Ef.Lv>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ee.fwd(xs: List<&2, Ef.Lv>, +c: Ef.Lv, +top: Ef.Lv) -> {Ef.fwd.go(xs, c, top, Ef.at(xs, c)) == EffortEntry.es.after(xs, c, top) : Maybe<&2, Ef.Lv>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %ee.fwd(rest, c, top) : {Ef.fwd.go(x <> rest, c, top, Ef.Lv.eq(x, c)) == EffortEntry.es.if(Maybe<&2, Ef.Lv>, EffortEntry.es.same(x, c), Some{EffortEntry.es.first(rest, top)}, _) : Maybe<&2, Ef.Lv>}
      %ee.first(rest, top) : {Ef.fwd.go(x <> rest, c, top, Ef.Lv.eq(x, c)) == EffortEntry.es.if(Maybe<&2, Ef.Lv>, EffortEntry.es.same(x, c), Some{_}, Ef.fwd.go(rest, c, top, Ef.at(rest, c))) : Maybe<&2, Ef.Lv>}
      %ee.eq(x, c) : {Ef.fwd.go(x <> rest, c, top, Ef.Lv.eq(x, c)) == EffortEntry.es.if(Maybe<&2, Ef.Lv>, _, Some{Ef.first(rest, top)}, Ef.fwd.go(rest, c, top, Ef.at(rest, c))) : Maybe<&2, Ef.Lv>}
      ee.fwd_step(Ef.Lv.eq(x, c), x, rest, c, top)

def ee.bwd_step(b: Bool, +x: Ef.Lv, +rest: List<&2, Ef.Lv>, +c: Ef.Lv, +prev: Ef.Lv) -> {Ef.bwd.go(x <> rest, c, prev, b) == EffortEntry.es.if(Maybe<&2, Ef.Lv>, b, Some{prev}, Ef.bwd.go(rest, c, x, Ef.at(rest, c))) : Maybe<&2, Ef.Lv>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ee.bwd(xs: List<&2, Ef.Lv>, +c: Ef.Lv, +prev: Ef.Lv) -> {Ef.bwd.go(xs, c, prev, Ef.at(xs, c)) == EffortEntry.es.before(xs, c, prev) : Maybe<&2, Ef.Lv>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      %ee.bwd(rest, c, x) : {Ef.bwd.go(x <> rest, c, prev, Ef.Lv.eq(x, c)) == EffortEntry.es.if(Maybe<&2, Ef.Lv>, EffortEntry.es.same(x, c), Some{prev}, _) : Maybe<&2, Ef.Lv>}
      %ee.eq(x, c) : {Ef.bwd.go(x <> rest, c, prev, Ef.Lv.eq(x, c)) == EffortEntry.es.if(Maybe<&2, Ef.Lv>, _, Some{prev}, Ef.bwd.go(rest, c, x, Ef.at(rest, c))) : Maybe<&2, Ef.Lv>}
      ee.bwd_step(Ef.Lv.eq(x, c), x, rest, c, prev)

def ee.move(d: Ef.Dir, +lad: List<&2, Ef.Lv>, +c: Ef.Lv) -> {Ef.move(d, lad, c) == EffortEntry.es.step(d, lad, c) : Maybe<&2, Ef.Lv>}:
  match d:
    case Ef.Forward{}:
      %ee.first(lad, Ef.Off{}) : {Ef.move(Ef.Forward{}, lad, c) == EffortEntry.es.after(lad, c, _) : Maybe<&2, Ef.Lv>}
      ee.fwd(lad, c, Ef.first(lad, Ef.Off{}))
    case Ef.Backward{}:
      %ee.last(lad, Ef.Off{}) : {Ef.move(Ef.Backward{}, lad, c) == EffortEntry.es.before(lad, c, _) : Maybe<&2, Ef.Lv>}
      ee.bwd(lad, c, Ef.last(lad, Ef.Off{}))

def ee.cycle_at(b: Bool, +lad: List<&2, Ef.Lv>, +l: Ef.Lv, d: Ef.Dir) -> {Ef.cycle.at(b, lad, l, d) == EffortEntry.es.if(Maybe<&2, Ef.Lv>, b, EffortEntry.es.step(d, lad, EffortEntry.es.clamp(lad, l)), None{}) : Maybe<&2, Ef.Lv>}:
  match b:
    case True{}:
      %ee.clamp(lad, l) : {Ef.move(d, lad, Ef.clamp.in(lad, l)) == EffortEntry.es.step(d, lad, _) : Maybe<&2, Ef.Lv>}
      ee.move(d, lad, Ef.clamp.in(lad, l))
    case False{}:
      {==}

def ee.cycle(+lad: List<&2, Ef.Lv>, +l: Ef.Lv, d: Ef.Dir) -> {Ef.cycle.in(lad, l, d) == EffortEntry.es.cycle(lad, l, d) : Maybe<&2, Ef.Lv>}:
  %ee.two(lad) : {Ef.cycle.in(lad, l, d) == EffortEntry.es.if(Maybe<&2, Ef.Lv>, _, EffortEntry.es.step(d, lad, EffortEntry.es.clamp(lad, l)), None{}) : Maybe<&2, Ef.Lv>}
  ee.cycle_at(Ef.two(lad), lad, l, d)

# Spelling
# --------

def ee.put_lv(l: Ef.Lv, rest: String) -> {FEf.put_lv(l, rest) == EffortEntry.es.lv(l, rest) : String}:
  match l:
    case Ef.Off{}:
      {==}
    case Ef.Minimal{}:
      {==}
    case Ef.Low{}:
      {==}
    case Ef.Medium{}:
      {==}
    case Ef.High{}:
      {==}
    case Ef.Xhigh{}:
      {==}
    case Ef.Max{}:
      {==}

def ee.put_mlv(m: Maybe<&2, Ef.Lv>, rest: String) -> {FEf.put_mlv(m, rest) == EffortEntry.es.mlv(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{l}:
      %ee.put_lv(l, rest) : {Wr.put_nat(1n, FEf.put_lv(l, rest)) == Wr.put_nat(1n, _) : String}
      {==}

def ee.answer(q: FEf.Req) -> {FEf.answer(q) == EffortEntry.es.reply(q) : String}:
  match q:
    case FEf.Offered{+f}:
      %ee.offered(f) : {Wr.put_list(~Ef.Lv, ~FEf.put_lv, Ef.offered(FEf.model(f)), "") == Wr.put_list(~Ef.Lv, ~EffortEntry.es.lv, _, "") : String}
      LX.lx.put(~Ef.Lv, ~FEf.put_lv, ~EffortEntry.es.lv, ~ee.put_lv, Ef.offered(FEf.model(f)), "")
    case FEf.Clamp{+f, +l}:
      %ee.offered(f) : {FEf.put_lv(Ef.clamp(FEf.model(f), l), "") == EffortEntry.es.lv(EffortEntry.es.clamp(_, l), "") : String}
      %ee.clamp(Ef.offered(FEf.model(f)), l) : {FEf.put_lv(Ef.clamp(FEf.model(f), l), "") == EffortEntry.es.lv(_, "") : String}
      ee.put_lv(Ef.clamp(FEf.model(f), l), "")
    case FEf.Cycle{+f, +l, +d}:
      %ee.offered(f) : {FEf.put_mlv(Ef.cycle(FEf.model(f), l, d), "") == EffortEntry.es.mlv(EffortEntry.es.cycle(_, l, d), "") : String}
      %ee.cycle(Ef.offered(FEf.model(f)), l, d) : {FEf.put_mlv(Ef.cycle(FEf.model(f), l, d), "") == EffortEntry.es.mlv(_, "") : String}
      ee.put_mlv(Ef.cycle(FEf.model(f), l, d), "")

# The entry
# ---------

def ee.end(b: Bool, q: FEf.Req) -> {FEf.ffi.done(b, q) == EffortEntry.es.end(b, q) : String}:
  match b:
    case True{}:
      ee.answer(q)
    case False{}:
      {==}

def ee.run(r: Wr.Dec<FEf.Req>) -> {FEf.ffi.go(r) == EffortEntry.es.run(r) : String}:
  match r:
    case Wr.Got{q, +s}:
      ee.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def EffortEntry.core_effort_ffi_exact(s):
  %ee.req(Wr.get_nat(s)) : {FEf.ffi.go(FEf.get_req(s)) == EffortEntry.es.run(_) : String}
  ee.run(FEf.get_req(s))
