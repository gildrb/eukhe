# eukhe: lemmas of the model_name entry proofs: each decoder stage answers
# Got only for the spelling of what it read, every count, length and Nat
# within the wire (the stage carries `pre`, the input spelled up to its
# field; lists: a loop predicate with the count, the dcw.ents pattern of
# proof/doc_commit/entry/list_ents.bend).

import Base
import ../../../bend/model_name.bend as M
import ../../../bend/ffi_model_name.bend as FM
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/model_name.bend as ModelName
import ../../wire/wire_strs_exact.bend as PWireStrsExact
import ../../wire/wire_strs_decoded_fit.bend as PWireStrsDecodedFit
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_str_exact.bend as PWireStrExact
import ../../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../base.bend as LA

def mnx.app(-s: String, +k: Nat, -s0: String, -y: String, pre: {s == Wr.put_nat(k, s0) : String}, e: {s0 == y : String}) -> {s == Wr.put_nat(k, y) : String}:
  Equal.trans(String, s, Wr.put_nat(k, s0), Wr.put_nat(k, y), pre, Equal.cong(String, String, z => Wr.put_nat(k, z), s0, y, e))

# A rule
# ------

def mnx.RulP(s: String, d: Wr.Dec<M.Rule>) -> Type:
  match d:
    case Wr.Got{r, rest}:
      {s == ModelName.sp_w_rule(r, rest) : String} & {ModelName.sp_fit_rule(r) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def mnx.contains(-s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<List<&2, String>>, ed: {FM.get_strs(s0) == d : Wr.Dec<List<&2, String>>}) -> mnx.RulP(s, FM.get_rule.contains(d)):
  match d:
    case Wr.Got{+ps, +rr}:
      +ee = ed
      (mnx.app(s, 0n, s0, LawsBase.wire_spell_strs(ps, rr), pre, Wire.wire_strs_exact(s0, ps, rr, ee)), Wire.wire_strs_decoded_fit(s0, ps, rr, ee))
    case Wr.Bad{}:
      Unit{}

def mnx.is(-s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<List<&2, String>>, ed: {FM.get_strs(s0) == d : Wr.Dec<List<&2, String>>}) -> mnx.RulP(s, FM.get_rule.is(d)):
  match d:
    case Wr.Got{+ps, +rr}:
      +ee = ed
      (mnx.app(s, 1n, s0, LawsBase.wire_spell_strs(ps, rr), pre, Wire.wire_strs_exact(s0, ps, rr, ee)), Wire.wire_strs_decoded_fit(s0, ps, rr, ee))
    case Wr.Bad{}:
      Unit{}

def mnx.starts(-s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<List<&2, String>>, ed: {FM.get_strs(s0) == d : Wr.Dec<List<&2, String>>}) -> mnx.RulP(s, FM.get_rule.starts(d)):
  match d:
    case Wr.Got{+ps, +rr}:
      +ee = ed
      (mnx.app(s, 2n, s0, LawsBase.wire_spell_strs(ps, rr), pre, Wire.wire_strs_exact(s0, ps, rr, ee)), Wire.wire_strs_decoded_fit(s0, ps, rr, ee))
    case Wr.Bad{}:
      Unit{}

def mnx.segment(-s: String, +s0: String, pre: {s == Wr.put_nat(5n, s0) : String}, d: Wr.Dec<List<&2, String>>, ed: {FM.get_strs(s0) == d : Wr.Dec<List<&2, String>>}) -> mnx.RulP(s, FM.get_rule.segment(d)):
  match d:
    case Wr.Got{+ps, +rr}:
      +ee = ed
      (mnx.app(s, 5n, s0, LawsBase.wire_spell_strs(ps, rr), pre, Wire.wire_strs_exact(s0, ps, rr, ee)), Wire.wire_strs_decoded_fit(s0, ps, rr, ee))
    case Wr.Bad{}:
      Unit{}

def mnx.then_b(-s: String, +a: String, +s1: String, pre: {s == Wr.put_nat(3n, Wr.put_str(a, s1)) : String}, fa: {LawsBase.wire_fits(String.length(a)) == True{} : Bool}, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}) -> mnx.RulP(s, FM.get_rule.then_b(a, d)):
  match d:
    case Wr.Got{+b, +rr}:
      +ee = ed
      (Equal.trans(String, s, Wr.put_nat(3n, Wr.put_str(a, s1)), Wr.put_nat(3n, Wr.put_str(a, Wr.put_str(b, rr))), pre, Equal.cong(String, String, z => Wr.put_nat(3n, Wr.put_str(a, z)), s1, Wr.put_str(b, rr), Wire.wire_str_exact(s1, b, rr, ee))), LA.mnb.and_t(LawsBase.wire_fits(String.length(a)), LawsBase.wire_fits(String.length(b)), fa, Wire.wire_str_decoded_fits(s1, b, rr, ee)))
    case Wr.Bad{}:
      Unit{}

def mnx.then_a(-s: String, +s0: String, pre: {s == Wr.put_nat(3n, s0) : String}, d: Wr.Dec<String>, ed: {Wr.get_str(s0) == d : Wr.Dec<String>}) -> mnx.RulP(s, FM.get_rule.then_a(d)):
  match d:
    case Wr.Got{+a, +s1}:
      +ee = ed
      mnx.then_b(s, a, s1, mnx.app(s, 3n, s0, Wr.put_str(a, s1), pre, Wire.wire_str_exact(s0, a, s1, ee)), Wire.wire_str_decoded_fits(s0, a, s1, ee), Wr.get_str(s1), {==})
    case Wr.Bad{}:
      Unit{}

def mnx.whole(-s: String, +ps: List<&2, String>, +n: Nat, +s2: String, pre: {s == Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, Wr.put_nat(n, s2))) : String}, fps: {LawsBase.wire_strs_fit(ps) == True{} : Bool}, fn: {LawsBase.wire_fits(n) == True{} : Bool}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s2) == d : Wr.Dec<Bool>}) -> mnx.RulP(s, FM.get_rule.whole(ps, n, d)):
  match d:
    case Wr.Got{+w, +rr}:
      +ee = ed
      (Equal.trans(String, s, Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, Wr.put_nat(n, s2))), Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, Wr.put_nat(n, Wr.put_bool(w, rr)))), pre, Equal.cong(String, String, z => Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, Wr.put_nat(n, z))), s2, Wr.put_bool(w, rr), Wire.wire_bool_exact(s2, w, rr, ee))), LA.mnb.and_t(LawsBase.wire_strs_fit(ps), LawsBase.wire_fits(n), fps, fn))
    case Wr.Bad{}:
      Unit{}

def mnx.least(-s: String, +ps: List<&2, String>, +s1: String, pre: {s == Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, s1)) : String}, fps: {LawsBase.wire_strs_fit(ps) == True{} : Bool}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s1) == d : Wr.Dec<Nat>}) -> mnx.RulP(s, FM.get_rule.least(ps, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +ee = ed
      mnx.whole(s, ps, n, s2, Equal.trans(String, s, Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, s1)), Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, Wr.put_nat(n, s2))), pre, Equal.cong(String, String, z => Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, z)), s1, Wr.put_nat(n, s2), Wire.wire_nat_exact(s1, n, s2, ee))), fps, Wire.wire_nat_decoded_fits(s1, n, s2, ee), Wr.get_bool(s2), {==})
    case Wr.Bad{}:
      Unit{}

def mnx.after(-s: String, +s0: String, pre: {s == Wr.put_nat(4n, s0) : String}, d: Wr.Dec<List<&2, String>>, ed: {FM.get_strs(s0) == d : Wr.Dec<List<&2, String>>}) -> mnx.RulP(s, FM.get_rule.after(d)):
  match d:
    case Wr.Got{+ps, +s1}:
      +ee = ed
      mnx.least(s, ps, s1, mnx.app(s, 4n, s0, LawsBase.wire_spell_strs(ps, s1), pre, Wire.wire_strs_exact(s0, ps, s1, ee)), Wire.wire_strs_decoded_fit(s0, ps, s1, ee), Wr.get_nat(s1), {==})
    case Wr.Bad{}:
      Unit{}

def mnx.rule_tag(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> mnx.RulP(s, FM.get_rule.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          mnx.contains(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), FM.get_strs(s0), {==})
        case 1n:
          mnx.is(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), FM.get_strs(s0), {==})
        case 2n:
          mnx.starts(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), FM.get_strs(s0), {==})
        case 3n:
          mnx.then_a(s, s0, Wire.wire_nat_exact(s, 3n, s0, ed), Wr.get_str(s0), {==})
        case 4n:
          mnx.after(s, s0, Wire.wire_nat_exact(s, 4n, s0, ed), FM.get_strs(s0), {==})
        case 5n:
          mnx.segment(s, s0, Wire.wire_nat_exact(s, 5n, s0, ed), FM.get_strs(s0), {==})
        case 6n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a rule decoded is spelled, and fits
def mnx.rule(+s: String) -> mnx.RulP(s, FM.get_rule(s)):
  mnx.rule_tag(s, Wr.get_nat(s), {==})

# A set (a list of rules)
# -----------------------

def mnx.RPL(s: String, m: Nat, d: Wr.Dec<List<&2, M.Rule>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ModelName.sp_w_rules.items(xs, r) : String} & ({List.length(&2, M.Rule, xs) == 1n+m : Nat} & {ModelName.sp_fit_rules(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def mnx.r_step(-s: String, +x: M.Rule, +s3: String, -k: Nat, ex: {s == ModelName.sp_w_rule(x, s3) : String}, fx: {ModelName.sp_fit_rule(x) == True{} : Bool}, d: Wr.Dec<List<&2, M.Rule>>, ih: mnx.RPL(s3, k, d)) -> mnx.RPL(s, 1n+k, Wr.get_list.cons(M.Rule, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, ModelName.sp_w_rule(x, s3), ModelName.sp_w_rule(x, ModelName.sp_w_rules.items(ys, r)), ex, Equal.cong(String, String, z => ModelName.sp_w_rule(x, z), s3, ModelName.sp_w_rules.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, M.Rule, ys), 1n+k, e2), LA.mnb.and_t(ModelName.sp_fit_rule(x), ModelName.sp_fit_rules(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def mnx.r_loop(m: Nat, cur: Wr.Dec<M.Rule>, +s: String, pc: mnx.RulP(s, cur)) -> mnx.RPL(s, m, Wr.get_list.go(~M.Rule, ~FM.get_rule, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LA.mnb.and_t(ModelName.sp_fit_rule(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      mnx.r_step(s, x, s3, k, e, f, Wr.get_list.go(~M.Rule, ~FM.get_rule, k, FM.get_rule(s3)), mnx.r_loop(k, FM.get_rule(s3), s3, mnx.rule(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def mnx.RLS(s: String, d: Wr.Dec<List<&2, M.Rule>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ModelName.sp_w_rules(xs, r) : String} & {ModelName.sp_fit_set(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def mnx.r_conv(-s: String, -s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, M.Rule>>, pl: mnx.RPL(s2, m, d)) -> mnx.RLS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      +es = mnx.app(s, 1n+m, s2, ModelName.sp_w_rules.items(xs, r), en, e1)
      +el = Equal.sym(Nat, List.length(&2, M.Rule, xs), 1n+m, e2)
      (Equal.trans(String, s, Wr.put_nat(1n+m, ModelName.sp_w_rules.items(xs, r)), Wr.put_nat(List.length(&2, M.Rule, xs), ModelName.sp_w_rules.items(xs, r)), es, Equal.cong(Nat, String, k => Wr.put_nat(k, ModelName.sp_w_rules.items(xs, r)), 1n+m, List.length(&2, M.Rule, xs), el)), LA.mnb.and_t(LawsBase.wire_fits(List.length(&2, M.Rule, xs)), ModelName.sp_fit_rules(xs), Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, M.Rule, xs)), LawsBase.wire_fits(1n+m), True{}, Equal.cong(Nat, Bool, k => LawsBase.wire_fits(k), List.length(&2, M.Rule, xs), 1n+m, e2), fn), e3))
    case Wr.Bad{}:
      Unit{}

def mnx.r_nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> mnx.RLS(s, Wr.get_list.start(~M.Rule, ~FM.get_rule, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, LA.mnb.and_t(LawsBase.wire_fits(0n), True{}, fn, {==}))
    case 1n++m:
      mnx.r_conv(s, s2, m, en, fn, Wr.get_list.go(~M.Rule, ~FM.get_rule, m, FM.get_rule(s2)), mnx.r_loop(m, FM.get_rule(s2), s2, mnx.rule(s2)))

def mnx.r_top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> mnx.RLS(s, Wr.get_list.start(~M.Rule, ~FM.get_rule, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      mnx.r_nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# a set decoded is spelled, and fits
def mnx.set(+s: String) -> mnx.RLS(s, FM.get_set(s)):
  mnx.r_top(s, Wr.get_nat(s), {==})

# The sets
# --------

def mnx.SPL(s: String, m: Nat, d: Wr.Dec<List<&2, List<&2, M.Rule>>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ModelName.sp_w_sets.items(xs, r) : String} & ({List.length(&2, List<&2, M.Rule>, xs) == 1n+m : Nat} & {ModelName.sp_fit_sets.all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def mnx.s_step(-s: String, +x: List<&2, M.Rule>, +s3: String, -k: Nat, ex: {s == ModelName.sp_w_rules(x, s3) : String}, fx: {ModelName.sp_fit_set(x) == True{} : Bool}, d: Wr.Dec<List<&2, List<&2, M.Rule>>>, ih: mnx.SPL(s3, k, d)) -> mnx.SPL(s, 1n+k, Wr.get_list.cons(List<&2, M.Rule>, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, ModelName.sp_w_rules(x, s3), ModelName.sp_w_rules(x, ModelName.sp_w_sets.items(ys, r)), ex, Equal.cong(String, String, z => ModelName.sp_w_rules(x, z), s3, ModelName.sp_w_sets.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, List<&2, M.Rule>, ys), 1n+k, e2), LA.mnb.and_t(ModelName.sp_fit_set(x), ModelName.sp_fit_sets.all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def mnx.s_loop(m: Nat, cur: Wr.Dec<List<&2, M.Rule>>, +s: String, pc: mnx.RLS(s, cur)) -> mnx.SPL(s, m, Wr.get_list.go(~List<&2, M.Rule>, ~FM.get_set, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LA.mnb.and_t(ModelName.sp_fit_set(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      mnx.s_step(s, x, s3, k, e, f, Wr.get_list.go(~List<&2, M.Rule>, ~FM.get_set, k, FM.get_set(s3)), mnx.s_loop(k, FM.get_set(s3), s3, mnx.set(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def mnx.SLS(s: String, d: Wr.Dec<List<&2, List<&2, M.Rule>>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ModelName.sp_w_sets(xs, r) : String} & {ModelName.sp_fit_sets(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def mnx.s_conv(-s: String, -s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, List<&2, M.Rule>>>, pl: mnx.SPL(s2, m, d)) -> mnx.SLS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      +es = mnx.app(s, 1n+m, s2, ModelName.sp_w_sets.items(xs, r), en, e1)
      +el = Equal.sym(Nat, List.length(&2, List<&2, M.Rule>, xs), 1n+m, e2)
      (Equal.trans(String, s, Wr.put_nat(1n+m, ModelName.sp_w_sets.items(xs, r)), Wr.put_nat(List.length(&2, List<&2, M.Rule>, xs), ModelName.sp_w_sets.items(xs, r)), es, Equal.cong(Nat, String, k => Wr.put_nat(k, ModelName.sp_w_sets.items(xs, r)), 1n+m, List.length(&2, List<&2, M.Rule>, xs), el)), LA.mnb.and_t(LawsBase.wire_fits(List.length(&2, List<&2, M.Rule>, xs)), ModelName.sp_fit_sets.all(xs), Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, List<&2, M.Rule>, xs)), LawsBase.wire_fits(1n+m), True{}, Equal.cong(Nat, Bool, k => LawsBase.wire_fits(k), List.length(&2, List<&2, M.Rule>, xs), 1n+m, e2), fn), e3))
    case Wr.Bad{}:
      Unit{}

def mnx.s_nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> mnx.SLS(s, Wr.get_list.start(~List<&2, M.Rule>, ~FM.get_set, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, LA.mnb.and_t(LawsBase.wire_fits(0n), True{}, fn, {==}))
    case 1n++m:
      mnx.s_conv(s, s2, m, en, fn, Wr.get_list.go(~List<&2, M.Rule>, ~FM.get_set, m, FM.get_set(s2)), mnx.s_loop(m, FM.get_set(s2), s2, mnx.set(s2)))

def mnx.s_top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> mnx.SLS(s, Wr.get_list.start(~List<&2, M.Rule>, ~FM.get_set, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      mnx.s_nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# the sets decoded are spelled, and fit
def mnx.sets(+s: String) -> mnx.SLS(s, Wr.get_list(~List<&2, M.Rule>, ~FM.get_set, s)):
  mnx.s_top(s, Wr.get_nat(s), {==})

# The groups
# ----------

def mnx.GP(s: String, d: Wr.Dec<List<&2, String>>) -> Type:
  match d:
    case Wr.Got{g, r}:
      {s == LawsBase.wire_spell_strs(g, r) : String} & {LawsBase.wire_strs_fit(g) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def mnx.strs_at(+s: String, d: Wr.Dec<List<&2, String>>, ed: {FM.get_strs(s) == d : Wr.Dec<List<&2, String>>}) -> mnx.GP(s, d):
  match d:
    case Wr.Got{+g, +r}:
      +ee = ed
      (Wire.wire_strs_exact(s, g, r, ee), Wire.wire_strs_decoded_fit(s, g, r, ee))
    case Wr.Bad{}:
      Unit{}

def mnx.strs(+s: String) -> mnx.GP(s, FM.get_strs(s)):
  mnx.strs_at(s, FM.get_strs(s), {==})

def mnx.GPL(s: String, m: Nat, d: Wr.Dec<List<&2, List<&2, String>>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ModelName.sp_w_groups.items(xs, r) : String} & ({List.length(&2, List<&2, String>, xs) == 1n+m : Nat} & {ModelName.sp_fit_groups.all(xs) == True{} : Bool})
    case Wr.Bad{}:
      Unit

def mnx.g_step(-s: String, +x: List<&2, String>, +s3: String, -k: Nat, ex: {s == LawsBase.wire_spell_strs(x, s3) : String}, fx: {LawsBase.wire_strs_fit(x) == True{} : Bool}, d: Wr.Dec<List<&2, List<&2, String>>>, ih: mnx.GPL(s3, k, d)) -> mnx.GPL(s, 1n+k, Wr.get_list.cons(List<&2, String>, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e23) = ih
      (e2, e3) = e23
      (Equal.trans(String, s, LawsBase.wire_spell_strs(x, s3), LawsBase.wire_spell_strs(x, ModelName.sp_w_groups.items(ys, r)), ex, Equal.cong(String, String, z => LawsBase.wire_spell_strs(x, z), s3, ModelName.sp_w_groups.items(ys, r), e1)), (Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, List<&2, String>, ys), 1n+k, e2), LA.mnb.and_t(LawsBase.wire_strs_fit(x), ModelName.sp_fit_groups.all(ys), fx, e3)))
    case Wr.Bad{}:
      Unit{}

def mnx.g_loop(m: Nat, cur: Wr.Dec<List<&2, String>>, +s: String, pc: mnx.GP(s, cur)) -> mnx.GPL(s, m, Wr.get_list.go(~List<&2, String>, ~FM.get_strs, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (e, f) = pc
      (e, ({==}, LA.mnb.and_t(LawsBase.wire_strs_fit(x), True{}, f, {==})))
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      (e, f) = pc
      mnx.g_step(s, x, s3, k, e, f, Wr.get_list.go(~List<&2, String>, ~FM.get_strs, k, FM.get_strs(s3)), mnx.g_loop(k, FM.get_strs(s3), s3, mnx.strs(s3)))
    case 1n++k Wr.Bad{}:
      Unit{}

def mnx.GLS(s: String, d: Wr.Dec<List<&2, List<&2, String>>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == ModelName.sp_w_groups(xs, r) : String} & {ModelName.sp_fit_groups(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def mnx.g_conv(-s: String, -s2: String, +m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String}, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, List<&2, String>>>, pl: mnx.GPL(s2, m, d)) -> mnx.GLS(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e23) = pl
      (+e2, e3) = e23
      +es = mnx.app(s, 1n+m, s2, ModelName.sp_w_groups.items(xs, r), en, e1)
      +el = Equal.sym(Nat, List.length(&2, List<&2, String>, xs), 1n+m, e2)
      (Equal.trans(String, s, Wr.put_nat(1n+m, ModelName.sp_w_groups.items(xs, r)), Wr.put_nat(List.length(&2, List<&2, String>, xs), ModelName.sp_w_groups.items(xs, r)), es, Equal.cong(Nat, String, k => Wr.put_nat(k, ModelName.sp_w_groups.items(xs, r)), 1n+m, List.length(&2, List<&2, String>, xs), el)), LA.mnb.and_t(LawsBase.wire_fits(List.length(&2, List<&2, String>, xs)), ModelName.sp_fit_groups.all(xs), Equal.trans(Bool, LawsBase.wire_fits(List.length(&2, List<&2, String>, xs)), LawsBase.wire_fits(1n+m), True{}, Equal.cong(Nat, Bool, k => LawsBase.wire_fits(k), List.length(&2, List<&2, String>, xs), 1n+m, e2), fn), e3))
    case Wr.Bad{}:
      Unit{}

def mnx.g_nat(-s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> mnx.GLS(s, Wr.get_list.start(~List<&2, String>, ~FM.get_strs, Wr.Got{n, s2})):
  match n:
    case 0n:
      (en, LA.mnb.and_t(LawsBase.wire_fits(0n), True{}, fn, {==}))
    case 1n++m:
      mnx.g_conv(s, s2, m, en, fn, Wr.get_list.go(~List<&2, String>, ~FM.get_strs, m, FM.get_strs(s2)), mnx.g_loop(m, FM.get_strs(s2), s2, mnx.strs(s2)))

def mnx.g_top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> mnx.GLS(s, Wr.get_list.start(~List<&2, String>, ~FM.get_strs, d)):
  match d:
    case Wr.Got{+n, +s2}:
      +e = ed
      mnx.g_nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, e), Wire.wire_nat_decoded_fits(s, n, s2, e))
    case Wr.Bad{}:
      Unit{}

# the groups decoded are spelled, and fit
def mnx.groups(+s: String) -> mnx.GLS(s, Wr.get_list(~List<&2, String>, ~FM.get_strs, s)):
  mnx.g_top(s, Wr.get_nat(s), {==})

# The request
# -----------

def mnx.RP(s: String, d: Wr.Dec<FM.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == ModelName.sp_w_req(q, r) : String} & {ModelName.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def mnx.x_groups(-s: String, +sets: List<&2, List<&2, M.Rule>>, +s1: String, pre: {s == Wr.put_nat(0n, ModelName.sp_w_sets(sets, s1)) : String}, fs: {ModelName.sp_fit_sets(sets) == True{} : Bool}, d: Wr.Dec<List<&2, List<&2, String>>>, gl: mnx.GLS(s1, d)) -> mnx.RP(s, FM.get_req.groups(sets, d)):
  match d:
    case Wr.Got{+gs, +r}:
      (e, f) = gl
      (Equal.trans(String, s, Wr.put_nat(0n, ModelName.sp_w_sets(sets, s1)), Wr.put_nat(0n, ModelName.sp_w_sets(sets, ModelName.sp_w_groups(gs, r))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, ModelName.sp_w_sets(sets, z)), s1, ModelName.sp_w_groups(gs, r), e)), LA.mnb.and_t(ModelName.sp_fit_sets(sets), ModelName.sp_fit_groups(gs), fs, f))
    case Wr.Bad{}:
      Unit{}

def mnx.x_sets(-s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<List<&2, List<&2, M.Rule>>>, sl: mnx.SLS(s0, d)) -> mnx.RP(s, FM.get_req.sets(d)):
  match d:
    case Wr.Got{+sets, +s1}:
      (e, f) = sl
      mnx.x_groups(s, sets, s1, mnx.app(s, 0n, s0, ModelName.sp_w_sets(sets, s1), pre, e), f, Wr.get_list(~List<&2, String>, ~FM.get_strs, s1), mnx.groups(s1))
    case Wr.Bad{}:
      Unit{}

def mnx.x_dash(-s: String, +s0: String, pre: {s == Wr.put_nat(1n, s0) : String}, d: Wr.Dec<List<&2, String>>, ed: {FM.get_strs(s0) == d : Wr.Dec<List<&2, String>>}) -> mnx.RP(s, FM.get_req.dash(d)):
  match d:
    case Wr.Got{+ts, +r}:
      +ee = ed
      (mnx.app(s, 1n, s0, LawsBase.wire_spell_strs(ts, r), pre, Wire.wire_strs_exact(s0, ts, r, ee)), Wire.wire_strs_decoded_fit(s0, ts, r, ee))
    case Wr.Bad{}:
      Unit{}

def mnx.x_req(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> mnx.RP(s, FM.get_req.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          mnx.x_sets(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), Wr.get_list(~List<&2, M.Rule>, ~FM.get_set, s0), mnx.sets(s0))
        case 1n:
          mnx.x_dash(s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), FM.get_strs(s0), {==})
        case 2n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# whatever the decoder reads from s is the spelling of what it read, then
# its rest, and fits the wire
def mnx.rp_all(+s: String) -> mnx.RP(s, FM.get_req(s)):
  mnx.x_req(s, Wr.get_nat(s), {==})
