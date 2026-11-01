# eukhe: lemmas of the model_name entry proofs: a spelled request that fits
# reads back (mne.req_rt), the answer is the spelled spec answer
# (mne.answer), and each decoder stage answers Got only for the spelling
# of what it read so far, every count, length and Nat within the wire
# (mne.rule_x, mne.set_x, mne.sets_x, mne.groups_x, mne.rp_all: the stage
# carries `pre`, the input spelled up to its field).

import Base
import ../../../bend/model_name.bend as M
import ../../../bend/ffi_model_name.bend as FM
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/model_name.bend as ModelName
import ../../wire/wire_strs_round_trip.bend as PWireStrsRoundTrip
import ../../wire/wire_strs_exact.bend as PWireStrsExact
import ../../wire/wire_strs_decoded_fit.bend as PWireStrsDecodedFit
import ../../wire/wire_strs_spells.bend as PWireStrsSpells
import ../../base/wire.bend as LBaseWire
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_str_exact.bend as PWireStrExact
import ../../wire/wire_str_decoded_fits.bend as PWireStrDecodedFits
import ../../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../wire/base/spell.bend as LAWireSpell
import ../base.bend as LA
import ./decide.bend as LD

# Reading back
# ------------

def mne.strs_rt(+xs: List<&2, String>, +rest: String, h: {LawsBase.wire_strs_fit(xs) == True{} : Bool}) -> {FM.get_strs(LawsBase.wire_spell_strs(xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, String>>}:
  Wire.wire_strs_round_trip(xs, rest, h)

# a spelled rule that fits reads back, the rest untouched
def mne.rule_rt(r: M.Rule, +rest: String, h: {ModelName.sp_fit_rule(r) == True{} : Bool}) -> {FM.get_rule(ModelName.sp_w_rule(r, rest)) == Wr.Got{r, rest} : Wr.Dec<M.Rule>}:
  match r:
    case M.RContains{+ps}:
      %Equal.sym(Wr.Dec<List<&2, String>>, FM.get_strs(LawsBase.wire_spell_strs(ps, rest)), Wr.Got{ps, rest}, mne.strs_rt(ps, rest, h)) : {FM.get_rule.contains(_) == Wr.Got{M.RContains{ps}, rest} : Wr.Dec<M.Rule>}
      {==}
    case M.RIs{+ps}:
      %Equal.sym(Wr.Dec<List<&2, String>>, FM.get_strs(LawsBase.wire_spell_strs(ps, rest)), Wr.Got{ps, rest}, mne.strs_rt(ps, rest, h)) : {FM.get_rule.is(_) == Wr.Got{M.RIs{ps}, rest} : Wr.Dec<M.Rule>}
      {==}
    case M.RStarts{+ps}:
      %Equal.sym(Wr.Dec<List<&2, String>>, FM.get_strs(LawsBase.wire_spell_strs(ps, rest)), Wr.Got{ps, rest}, mne.strs_rt(ps, rest, h)) : {FM.get_rule.starts(_) == Wr.Got{M.RStarts{ps}, rest} : Wr.Dec<M.Rule>}
      {==}
    case M.RThen{+a, +b}:
      +hh = h
      +x = Wr.put_str(b, rest)
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(a, x)), Wr.Got{a, x}, Wire.wire_str_round_trip(a, x, LA.mnb.and_l(LawsBase.wire_fits(String.length(a)), LawsBase.wire_fits(String.length(b)), hh))) : {FM.get_rule.then_a(_) == Wr.Got{M.RThen{a, b}, rest} : Wr.Dec<M.Rule>}
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(b, rest)), Wr.Got{b, rest}, Wire.wire_str_round_trip(b, rest, LA.mnb.and_r(LawsBase.wire_fits(String.length(a)), LawsBase.wire_fits(String.length(b)), hh))) : {FM.get_rule.then_b(a, _) == Wr.Got{M.RThen{a, b}, rest} : Wr.Dec<M.Rule>}
      {==}
    case M.RNumber{+ps, +n, +w}:
      +hh = h
      +x2 = Wr.put_bool(w, rest)
      +x1 = Wr.put_nat(n, x2)
      %Equal.sym(Wr.Dec<List<&2, String>>, FM.get_strs(LawsBase.wire_spell_strs(ps, x1)), Wr.Got{ps, x1}, mne.strs_rt(ps, x1, LA.mnb.and_l(LawsBase.wire_strs_fit(ps), LawsBase.wire_fits(n), hh))) : {FM.get_rule.after(_) == Wr.Got{M.RNumber{ps, n, w}, rest} : Wr.Dec<M.Rule>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, x2)), Wr.Got{n, x2}, Wire.wire_nat_round_trip(n, x2, LA.mnb.and_r(LawsBase.wire_strs_fit(ps), LawsBase.wire_fits(n), hh))) : {FM.get_rule.least(ps, _) == Wr.Got{M.RNumber{ps, n, w}, rest} : Wr.Dec<M.Rule>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(w, rest)), Wr.Got{w, rest}, Wire.wire_bool_round_trip(w, rest)) : {FM.get_rule.whole(ps, n, _) == Wr.Got{M.RNumber{ps, n, w}, rest} : Wr.Dec<M.Rule>}
      {==}
    case M.RSegment{+ps}:
      %Equal.sym(Wr.Dec<List<&2, String>>, FM.get_strs(LawsBase.wire_spell_strs(ps, rest)), Wr.Got{ps, rest}, mne.strs_rt(ps, rest, h)) : {FM.get_rule.segment(_) == Wr.Got{M.RSegment{ps}, rest} : Wr.Dec<M.Rule>}
      {==}

# the item loop reads back x then t (a set's rules)
def mne.rules_go(+t: List<&2, M.Rule>, +x: M.Rule, +rest: String, h: {ModelName.sp_fit_rules(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~M.Rule, ~FM.get_rule, List.length(&2, M.Rule, t), FM.get_rule(ModelName.sp_w_rule(x, ModelName.sp_w_rules.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, M.Rule>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<M.Rule>, FM.get_rule(ModelName.sp_w_rule(x, rest)), Wr.Got{x, rest}, mne.rule_rt(x, rest, LA.mnb.and_l(ModelName.sp_fit_rule(x), True{}, h))) : {Wr.get_list.go(~M.Rule, ~FM.get_rule, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, M.Rule>>}
      {==}
    case +y <> +u:
      +hh = h
      +r2 = ModelName.sp_w_rule(y, ModelName.sp_w_rules.items(u, rest))
      %Equal.sym(Wr.Dec<M.Rule>, FM.get_rule(ModelName.sp_w_rule(x, r2)), Wr.Got{x, r2}, mne.rule_rt(x, r2, LA.mnb.and_l(ModelName.sp_fit_rule(x), ModelName.sp_fit_rules(y <> u), hh))) : {Wr.get_list.go(~M.Rule, ~FM.get_rule, 1n+List.length(&2, M.Rule, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, M.Rule>>}
      %Equal.sym(Wr.Dec<List<&2, M.Rule>>, Wr.get_list.go(~M.Rule, ~FM.get_rule, List.length(&2, M.Rule, u), FM.get_rule(r2)), Wr.Got{y <> u, rest}, mne.rules_go(u, y, rest, LA.mnb.and_r(ModelName.sp_fit_rule(x), ModelName.sp_fit_rules(y <> u), hh))) : {Wr.get_list.cons(M.Rule, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, M.Rule>>}
      {==}

# a spelled set that fits reads back
def mne.set_rt(rs: List<&2, M.Rule>, +rest: String, h: {ModelName.sp_fit_set(rs) == True{} : Bool}) -> {FM.get_set(ModelName.sp_w_rules(rs, rest)) == Wr.Got{rs, rest} : Wr.Dec<List<&2, M.Rule>>}:
  match rs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, LA.mnb.and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~M.Rule, ~FM.get_rule, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, M.Rule>>}
      {==}
    case +x <> +t:
      +hh = h
      +n = List.length(&2, M.Rule, x <> t)
      +items = ModelName.sp_w_rules.items(x <> t, rest)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, items)), Wr.Got{n, items}, Wire.wire_nat_round_trip(n, items, LA.mnb.and_l(LawsBase.wire_fits(n), ModelName.sp_fit_rules(x <> t), hh))) : {Wr.get_list.start(~M.Rule, ~FM.get_rule, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, M.Rule>>}
      mne.rules_go(t, x, rest, LA.mnb.and_r(LawsBase.wire_fits(n), ModelName.sp_fit_rules(x <> t), hh))

# the item loop reads back x then t (the sets)
def mne.sets_go(+t: List<&2, List<&2, M.Rule>>, +x: List<&2, M.Rule>, +rest: String, h: {ModelName.sp_fit_sets.all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~List<&2, M.Rule>, ~FM.get_set, List.length(&2, List<&2, M.Rule>, t), FM.get_set(ModelName.sp_w_rules(x, ModelName.sp_w_sets.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, List<&2, M.Rule>>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<List<&2, M.Rule>>, FM.get_set(ModelName.sp_w_rules(x, rest)), Wr.Got{x, rest}, mne.set_rt(x, rest, LA.mnb.and_l(ModelName.sp_fit_set(x), True{}, h))) : {Wr.get_list.go(~List<&2, M.Rule>, ~FM.get_set, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, List<&2, M.Rule>>>}
      {==}
    case +y <> +u:
      +hh = h
      +r2 = ModelName.sp_w_rules(y, ModelName.sp_w_sets.items(u, rest))
      %Equal.sym(Wr.Dec<List<&2, M.Rule>>, FM.get_set(ModelName.sp_w_rules(x, r2)), Wr.Got{x, r2}, mne.set_rt(x, r2, LA.mnb.and_l(ModelName.sp_fit_set(x), ModelName.sp_fit_sets.all(y <> u), hh))) : {Wr.get_list.go(~List<&2, M.Rule>, ~FM.get_set, 1n+List.length(&2, List<&2, M.Rule>, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, List<&2, M.Rule>>>}
      %Equal.sym(Wr.Dec<List<&2, List<&2, M.Rule>>>, Wr.get_list.go(~List<&2, M.Rule>, ~FM.get_set, List.length(&2, List<&2, M.Rule>, u), FM.get_set(r2)), Wr.Got{y <> u, rest}, mne.sets_go(u, y, rest, LA.mnb.and_r(ModelName.sp_fit_set(x), ModelName.sp_fit_sets.all(y <> u), hh))) : {Wr.get_list.cons(List<&2, M.Rule>, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, List<&2, M.Rule>>>}
      {==}

# spelled sets that fit read back
def mne.sets_rt(sets: List<&2, List<&2, M.Rule>>, +rest: String, h: {ModelName.sp_fit_sets(sets) == True{} : Bool}) -> {Wr.get_list(~List<&2, M.Rule>, ~FM.get_set, ModelName.sp_w_sets(sets, rest)) == Wr.Got{sets, rest} : Wr.Dec<List<&2, List<&2, M.Rule>>>}:
  match sets:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, LA.mnb.and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~List<&2, M.Rule>, ~FM.get_set, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, List<&2, M.Rule>>>}
      {==}
    case +x <> +t:
      +hh = h
      +n = List.length(&2, List<&2, M.Rule>, x <> t)
      +items = ModelName.sp_w_sets.items(x <> t, rest)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, items)), Wr.Got{n, items}, Wire.wire_nat_round_trip(n, items, LA.mnb.and_l(LawsBase.wire_fits(n), ModelName.sp_fit_sets.all(x <> t), hh))) : {Wr.get_list.start(~List<&2, M.Rule>, ~FM.get_set, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, List<&2, M.Rule>>>}
      mne.sets_go(t, x, rest, LA.mnb.and_r(LawsBase.wire_fits(n), ModelName.sp_fit_sets.all(x <> t), hh))

# the item loop reads back x then t (the groups)
def mne.groups_go(+t: List<&2, List<&2, String>>, +x: List<&2, String>, +rest: String, h: {ModelName.sp_fit_groups.all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~List<&2, String>, ~FM.get_strs, List.length(&2, List<&2, String>, t), FM.get_strs(LawsBase.wire_spell_strs(x, ModelName.sp_w_groups.items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, List<&2, String>>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<List<&2, String>>, FM.get_strs(LawsBase.wire_spell_strs(x, rest)), Wr.Got{x, rest}, mne.strs_rt(x, rest, LA.mnb.and_l(LawsBase.wire_strs_fit(x), True{}, h))) : {Wr.get_list.go(~List<&2, String>, ~FM.get_strs, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, List<&2, String>>>}
      {==}
    case +y <> +u:
      +hh = h
      +r2 = LawsBase.wire_spell_strs(y, ModelName.sp_w_groups.items(u, rest))
      %Equal.sym(Wr.Dec<List<&2, String>>, FM.get_strs(LawsBase.wire_spell_strs(x, r2)), Wr.Got{x, r2}, mne.strs_rt(x, r2, LA.mnb.and_l(LawsBase.wire_strs_fit(x), ModelName.sp_fit_groups.all(y <> u), hh))) : {Wr.get_list.go(~List<&2, String>, ~FM.get_strs, 1n+List.length(&2, List<&2, String>, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, List<&2, String>>>}
      %Equal.sym(Wr.Dec<List<&2, List<&2, String>>>, Wr.get_list.go(~List<&2, String>, ~FM.get_strs, List.length(&2, List<&2, String>, u), FM.get_strs(r2)), Wr.Got{y <> u, rest}, mne.groups_go(u, y, rest, LA.mnb.and_r(LawsBase.wire_strs_fit(x), ModelName.sp_fit_groups.all(y <> u), hh))) : {Wr.get_list.cons(List<&2, String>, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, List<&2, String>>>}
      {==}

# spelled groups that fit read back
def mne.groups_rt(gs: List<&2, List<&2, String>>, +rest: String, h: {ModelName.sp_fit_groups(gs) == True{} : Bool}) -> {Wr.get_list(~List<&2, String>, ~FM.get_strs, ModelName.sp_w_groups(gs, rest)) == Wr.Got{gs, rest} : Wr.Dec<List<&2, List<&2, String>>>}:
  match gs:
    case Nil{}:
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(0n, rest)), Wr.Got{0n, rest}, Wire.wire_nat_round_trip(0n, rest, LA.mnb.and_l(LawsBase.wire_fits(0n), True{}, h))) : {Wr.get_list.start(~List<&2, String>, ~FM.get_strs, _) == Wr.Got{Nil{}, rest} : Wr.Dec<List<&2, List<&2, String>>>}
      {==}
    case +x <> +t:
      +hh = h
      +n = List.length(&2, List<&2, String>, x <> t)
      +items = ModelName.sp_w_groups.items(x <> t, rest)
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, items)), Wr.Got{n, items}, Wire.wire_nat_round_trip(n, items, LA.mnb.and_l(LawsBase.wire_fits(n), ModelName.sp_fit_groups.all(x <> t), hh))) : {Wr.get_list.start(~List<&2, String>, ~FM.get_strs, _) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, List<&2, String>>>}
      mne.groups_go(t, x, rest, LA.mnb.and_r(LawsBase.wire_fits(n), ModelName.sp_fit_groups.all(x <> t), hh))

# a spelled request that fits reads back, the rest untouched
def mne.req_rt(q: FM.Req, +rest: String, h: {ModelName.sp_fit_req(q) == True{} : Bool}) -> {FM.get_req(ModelName.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FM.Req>}:
  match q:
    case FM.QHolds{+sets, +gs}:
      +hh = h
      +x = ModelName.sp_w_groups(gs, rest)
      %Equal.sym(Wr.Dec<List<&2, List<&2, M.Rule>>>, Wr.get_list(~List<&2, M.Rule>, ~FM.get_set, ModelName.sp_w_sets(sets, x)), Wr.Got{sets, x}, mne.sets_rt(sets, x, LA.mnb.and_l(ModelName.sp_fit_sets(sets), ModelName.sp_fit_groups(gs), hh))) : {FM.get_req.sets(_) == Wr.Got{FM.QHolds{sets, gs}, rest} : Wr.Dec<FM.Req>}
      %Equal.sym(Wr.Dec<List<&2, List<&2, String>>>, Wr.get_list(~List<&2, String>, ~FM.get_strs, ModelName.sp_w_groups(gs, rest)), Wr.Got{gs, rest}, mne.groups_rt(gs, rest, LA.mnb.and_r(ModelName.sp_fit_sets(sets), ModelName.sp_fit_groups(gs), hh))) : {FM.get_req.groups(sets, _) == Wr.Got{FM.QHolds{sets, gs}, rest} : Wr.Dec<FM.Req>}
      {==}
    case FM.QDash{+ts}:
      %Equal.sym(Wr.Dec<List<&2, String>>, FM.get_strs(LawsBase.wire_spell_strs(ts, rest)), Wr.Got{ts, rest}, mne.strs_rt(ts, rest, h)) : {FM.get_req.dash(_) == Wr.Got{FM.QDash{ts}, rest} : Wr.Dec<FM.Req>}
      {==}

# The answer
# ----------

def mne.bools_go(xs: List<&2, Bool>, -rest: String) -> {Wr.put_list.go(~Bool, ~Wr.put_bool, xs, rest) == (List.length(&2, Bool, xs), ModelName.sp_w_bools.items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      %Equal.sym(Nat & String, Wr.put_list.go(~Bool, ~Wr.put_bool, t, rest), (List.length(&2, Bool, t), ModelName.sp_w_bools.items(t, rest)), mne.bools_go(t, rest)) : {Wr.put_list.step(~Bool, ~Wr.put_bool, x, _) == (1n+List.length(&2, Bool, t), Wr.put_bool(x, ModelName.sp_w_bools.items(t, rest))) : Nat & String}
      {==}

# a list of Bools is its count, then each Bool
def mne.bools(+xs: List<&2, Bool>, -rest: String) -> {Wr.put_list(~Bool, ~Wr.put_bool, xs, rest) == ModelName.sp_w_bools(xs, rest) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Bool, ~Wr.put_bool, xs, rest), (List.length(&2, Bool, xs), ModelName.sp_w_bools.items(xs, rest)), mne.bools_go(xs, rest)) : {Wr.put_list.fin(_) == ModelName.sp_w_bools(xs, rest) : String}
  {==}

def mne.dashes(ts: List<&2, String>) -> {M.dashes(ts) == ModelName.sp_dashes(ts) : List<&2, String>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> more:
      %Equal.sym(String, M.dash(t), ModelName.sp_dash(t), LD.mnd.dash_go(t, None{})) : {_ <> M.dashes(more) == ModelName.sp_dash(t) <> ModelName.sp_dashes(more) : List<&2, String>}
      Equal.cong(List<&2, String>, List<&2, String>, z => ModelName.sp_dash(t) <> z, M.dashes(more), ModelName.sp_dashes(more), mne.dashes(more))

# the entry's answer to a request is the spelled spec answer
def mne.answer(q: FM.Req) -> {FM.answer(q) == ModelName.sp_w_reply(q) : String}:
  match q:
    case FM.QHolds{+sets, +gs}:
      %Equal.sym(List<&2, Bool>, M.holds(sets, gs), ModelName.sp_verdicts(sets, gs), LD.mnd.holds(sets, gs)) : {Wr.put_list(~Bool, ~Wr.put_bool, _, "") == ModelName.sp_w_bools(ModelName.sp_verdicts(sets, gs), "") : String}
      mne.bools(ModelName.sp_verdicts(sets, gs), "")
    case FM.QDash{+ts}:
      %Equal.sym(List<&2, String>, M.dashes(ts), ModelName.sp_dashes(ts), mne.dashes(ts)) : {Wr.put_list(~String, ~Wr.put_str, _, "") == LawsBase.wire_spell_strs(ModelName.sp_dashes(ts), "") : String}
      Wire.wire_strs_spells(ModelName.sp_dashes(ts), "")
