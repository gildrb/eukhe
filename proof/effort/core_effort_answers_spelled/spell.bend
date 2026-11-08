# eukhe: the entry's encoders write what the laws spell
#
# The entry's put_* (bend/ffi_effort.bend) and the laws' grammar
# (laws/effort.bend core_effort_spell_*) give the same bytes on every
# value, field by field: a level, an entry and a direction tag by tag, a
# map entry by entry, a list its count then item by item.

import Base
import ../../../bend/effort.bend as Ef
import ../../../bend/ffi_effort.bend as FEf
import ../../../bend/wire.bend as Wr
import ../../../laws/effort/ladder.bend as EffortLadder
import ../base.bend as LA

# a level
def es.lv(l: Ef.Lv, rest: String) -> {FEf.put_lv(l, rest) == EffortLadder.core_effort_spell_lv(l, rest) : String}:
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

# an entry of a map
def es.ent(e: Ef.Ent, rest: String) -> {FEf.put_ent(e, rest) == EffortLadder.core_effort_spell_ent(e, rest) : String}:
  match e:
    case Ef.Missing{}:
      {==}
    case Ef.Null{}:
      {==}
    case Ef.Wire{}:
      {==}

# a direction
def es.dir(d: Ef.Dir, rest: String) -> {FEf.put_dir(d, rest) == EffortLadder.core_effort_spell_dir(d, rest) : String}:
  match d:
    case Ef.Forward{}:
      {==}
    case Ef.Backward{}:
      {==}

# an entry before equal rests
def es.ent2(+e: Ef.Ent, -a: String, +b: String, h: {a == b : String}) -> {FEf.put_ent(e, a) == EffortLadder.core_effort_spell_ent(e, b) : String}:
  Equal.trans(String, FEf.put_ent(e, a), FEf.put_ent(e, b), EffortLadder.core_effort_spell_ent(e, b), Equal.cong(String, String, z => FEf.put_ent(e, z), a, b, h), es.ent(e, b))

# a level before equal rests
def es.lv2(+l: Ef.Lv, -a: String, +b: String, h: {a == b : String}) -> {FEf.put_lv(l, a) == EffortLadder.core_effort_spell_lv(l, b) : String}:
  Equal.trans(String, FEf.put_lv(l, a), FEf.put_lv(l, b), EffortLadder.core_effort_spell_lv(l, b), Equal.cong(String, String, z => FEf.put_lv(l, z), a, b, h), es.lv(l, b))

# a map
def es.map(m: Ef.LvMap, +rest: String) -> {FEf.put_map(m, rest) == EffortLadder.core_effort_spell_map(m, rest) : String}:
  match m:
    case Ef.LvMap{+o, +mi, +lo, +me, +hi, +xh, +mx}:
      +s6 = EffortLadder.core_effort_spell_ent(mx, rest)
      +s5 = EffortLadder.core_effort_spell_ent(xh, s6)
      +s4 = EffortLadder.core_effort_spell_ent(hi, s5)
      +s3 = EffortLadder.core_effort_spell_ent(me, s4)
      +s2 = EffortLadder.core_effort_spell_ent(lo, s3)
      +s1 = EffortLadder.core_effort_spell_ent(mi, s2)
      +p6 = FEf.put_ent(mx, rest)
      +p5 = FEf.put_ent(xh, p6)
      +p4 = FEf.put_ent(hi, p5)
      +p3 = FEf.put_ent(me, p4)
      +p2 = FEf.put_ent(lo, p3)
      +p1 = FEf.put_ent(mi, p2)
      es.ent2(o, p1, s1, es.ent2(mi, p2, s2, es.ent2(lo, p3, s3, es.ent2(me, p4, s4, es.ent2(hi, p5, s5, es.ent2(xh, p6, s6, es.ent(mx, rest)))))))

# a map or none
def es.mmap(m: Maybe<&2, Ef.LvMap>, +rest: String) -> {FEf.put_mmap(m, rest) == EffortLadder.core_effort_spell_mmap(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), FEf.put_map(x, rest), EffortLadder.core_effort_spell_map(x, rest), es.map(x, rest))

# the items of a list of levels
def es.items(xs: List<&2, Ef.Lv>, +rest: String) -> {LA.pc.e_lv_items(xs, rest) == EffortLadder.core_effort_spell_lvs.items(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      es.lv2(x, LA.pc.e_lv_items(t, rest), EffortLadder.core_effort_spell_lvs.items(t, rest), es.items(t, rest))

# a list of levels: its count, then its items
def es.lvs(+xs: List<&2, Ef.Lv>, +rest: String) -> {Wr.put_list(~Ef.Lv, ~FEf.put_lv, xs, rest) == EffortLadder.core_effort_spell_lvs(xs, rest) : String}:
  Equal.trans(String, Wr.put_list(~Ef.Lv, ~FEf.put_lv, xs, rest), Wr.put_nat(List.length(&2, Ef.Lv, xs), LA.pc.e_lv_items(xs, rest)), EffortLadder.core_effort_spell_lvs(xs, rest), LA.pc.e_lv_put(xs, rest), Equal.cong(String, String, z => Wr.put_nat(List.length(&2, Ef.Lv, xs), z), LA.pc.e_lv_items(xs, rest), EffortLadder.core_effort_spell_lvs.items(xs, rest), es.items(xs, rest)))

# a list of levels before equal rests
def es.lvs2(+xs: List<&2, Ef.Lv>, -a: String, +b: String, h: {a == b : String}) -> {FEf.put_lvs(xs, a) == EffortLadder.core_effort_spell_lvs(xs, b) : String}:
  Equal.trans(String, FEf.put_lvs(xs, a), FEf.put_lvs(xs, b), EffortLadder.core_effort_spell_lvs(xs, b), Equal.cong(String, String, z => FEf.put_lvs(xs, z), a, b, h), es.lvs(xs, b))

# a map or none before equal rests
def es.mmap2(+m: Maybe<&2, Ef.LvMap>, -a: String, +b: String, h: {a == b : String}) -> {FEf.put_mmap(m, a) == EffortLadder.core_effort_spell_mmap(m, b) : String}:
  Equal.trans(String, FEf.put_mmap(m, a), FEf.put_mmap(m, b), EffortLadder.core_effort_spell_mmap(m, b), Equal.cong(String, String, z => FEf.put_mmap(m, z), a, b, h), es.mmap(m, b))

# the facts before equal rests
def es.facts2(f: FEf.Facts, +a: String, +b: String, h: {a == b : String}) -> {FEf.put_facts(f, a) == EffortLadder.core_effort_spell_facts(f, b) : String}:
  match f:
    case FEf.Facts{+flag, +by_map, +explicit, +rule, +reasoning, +plain}:
      +s4 = EffortLadder.core_effort_spell_lvs(plain, b)
      +s3 = EffortLadder.core_effort_spell_lvs(reasoning, s4)
      +s2 = EffortLadder.core_effort_spell_mmap(rule, s3)
      +s1 = EffortLadder.core_effort_spell_mmap(explicit, s2)
      +p4 = FEf.put_lvs(plain, a)
      +p3 = FEf.put_lvs(reasoning, p4)
      +p2 = FEf.put_mmap(rule, p3)
      +p1 = FEf.put_mmap(explicit, p2)
      Equal.cong(String, String, z => Wr.put_bool(flag, Wr.put_bool(by_map, z)), p1, s1, es.mmap2(explicit, p2, s2, es.mmap2(rule, p3, s3, es.lvs2(reasoning, p4, s4, es.lvs2(plain, a, b, h)))))

# a request
def es.req(q: FEf.Req, +rest: String) -> {FEf.put_req(q, rest) == EffortLadder.core_effort_spell_req(q, rest) : String}:
  match q:
    case FEf.Offered{+f}:
      Equal.cong(String, String, z => Wr.put_nat(0n, z), FEf.put_facts(f, rest), EffortLadder.core_effort_spell_facts(f, rest), es.facts2(f, rest, rest, {==}))
    case FEf.Clamp{+f, +l}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), FEf.put_facts(f, FEf.put_lv(l, rest)), EffortLadder.core_effort_spell_facts(f, EffortLadder.core_effort_spell_lv(l, rest)), es.facts2(f, FEf.put_lv(l, rest), EffortLadder.core_effort_spell_lv(l, rest), es.lv(l, rest)))
    case FEf.Cycle{+f, +l, +d}:
      Equal.cong(String, String, z => Wr.put_nat(2n, z), FEf.put_facts(f, FEf.put_lv(l, FEf.put_dir(d, rest))), EffortLadder.core_effort_spell_facts(f, EffortLadder.core_effort_spell_lv(l, EffortLadder.core_effort_spell_dir(d, rest))), es.facts2(f, FEf.put_lv(l, FEf.put_dir(d, rest)), EffortLadder.core_effort_spell_lv(l, EffortLadder.core_effort_spell_dir(d, rest)), es.lv2(l, FEf.put_dir(d, rest), EffortLadder.core_effort_spell_dir(d, rest), es.dir(d, rest))))

# a level or none
def es.mlv(m: Maybe<&2, Ef.Lv>, rest: String) -> {FEf.put_mlv(m, rest) == EffortLadder.core_effort_spell_mlv(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{+l}:
      Equal.cong(String, String, z => Wr.put_nat(1n, z), FEf.put_lv(l, rest), EffortLadder.core_effort_spell_lv(l, rest), es.lv(l, rest))

# the entry's reply to a request is the spelled reply (the entry's model
# of the facts is core_effort_model's)
def es.answer(q: FEf.Req) -> {FEf.answer(q) == EffortLadder.core_effort_spell_answer(q) : String}:
  match q:
    case FEf.Offered{f}:
      match f:
        case FEf.Facts{+flag, +by_map, +explicit, +rule, +reasoning, +plain}:
          es.lvs(Ef.offered(EffortLadder.core_effort_model(FEf.Facts{flag, by_map, explicit, rule, reasoning, plain})), "")
    case FEf.Clamp{f, +l}:
      match f:
        case FEf.Facts{+flag, +by_map, +explicit, +rule, +reasoning, +plain}:
          es.lv(Ef.clamp(EffortLadder.core_effort_model(FEf.Facts{flag, by_map, explicit, rule, reasoning, plain}), l), "")
    case FEf.Cycle{f, +l, +d}:
      match f:
        case FEf.Facts{+flag, +by_map, +explicit, +rule, +reasoning, +plain}:
          es.mlv(Ef.cycle(EffortLadder.core_effort_model(FEf.Facts{flag, by_map, explicit, rule, reasoning, plain}), l, d), "")

# a spelled request that fits reads back whole, the rest untouched
def es.read(+q: FEf.Req, +rest: String, h: {EffortLadder.core_effort_fits(q) == True{} : Bool}) -> {Wr.Got{q, rest} == FEf.get_req(EffortLadder.core_effort_spell_req(q, rest)) : Wr.Dec<FEf.Req>}:
  %es.req(q, rest) : {Wr.Got{q, rest} == FEf.get_req(_) : Wr.Dec<FEf.Req>}
  LA.pc.e_req(q, rest, h)

# a spelled request that fits, then rest, gets the entry's answer when
# nothing is left, the left-over error otherwise
def es.run(+q: FEf.Req, +rest: String, h: {EffortLadder.core_effort_fits(q) == True{} : Bool}) -> {FEf.ffi(EffortLadder.core_effort_spell_req(q, rest)) == FEf.ffi.done(Wr.end(rest), q) : String}:
  %es.read(q, rest, h) : {FEf.ffi.go(_) == FEf.ffi.done(Wr.end(rest), q) : String}
  {==}
