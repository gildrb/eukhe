# eukhe: lemmas the proofs of area path_policy share

import Base
import ../../bend/ffi_path_policy.bend as FPp
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../bend/wire_flat.bend as Fl
import ../../laws/base.bend as LawsBase
import ../../laws/path_policy/policy.bend as PathPolicy
import ../../laws/wire.bend as Wire
import ../base/logic/logic.bend as LLogicLogic
import ../wire/wire_nats_spells.bend as PWireNatsSpells

def pp.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : LLogicLogic.path_policy.pp.BD(_, A, Unit)
  Unit{}

def pp.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      pp.absurdF({b == True{} : Bool}, h)

def pp.or_tr(a: Bool, +b: Bool, hb: {b == True{} : Bool}) -> {Bool.or(a, b) == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      hb

# demote gives Inside only for an Inside that did not loop
def pp.demote_inside(c: Pp.Cls, looped: Bool, h: {Pp.demote(c, looped) == Pp.Inside{} : Pp.Cls}) -> {Bool.and(Bool.not(looped), Pp.Cls.inside(c)) == True{} : Bool}:
  match c:
    case Pp.Inside{}:
      match looped:
        case True{}:
          %h : LLogicLogic.pp.CM(_, {Bool.and(Bool.not(True{}), True{}) == True{} : Bool})
          Unit{}
        case False{}:
          {==}
    case Pp.Outside{}:
      %h : LLogicLogic.pp.CM(_, {Bool.and(Bool.not(looped), False{}) == True{} : Bool})
      Unit{}
    case Pp.Protected{}:
      %h : LLogicLogic.pp.CM(_, {Bool.and(Bool.not(looped), False{}) == True{} : Bool})
      Unit{}
    case Pp.Secret{}:
      %h : LLogicLogic.pp.CM(_, {Bool.and(Bool.not(looped), False{}) == True{} : Bool})
      Unit{}

# 3. The gate
# -----------

# a yes that is not a yes
def pp.yes_clash(-A: Type, ans: Pp.Ans, ran: {Pp.Ans.yes(ans) == True{} : Bool}, no: {Pp.Ans.yes(ans) == False{} : Bool}) -> A:
  LLogicLogic.pp.absurd(A, Equal.trans(Bool, True{}, Pp.Ans.yes(ans), False{}, Equal.sym(Bool, Pp.Ans.yes(ans), True{}, ran), no))

def pp.gate_write_auto_never_secret(c: Pp.Cls, +auto: List<&2, Nat>, +ans: Pp.Ans, ran: {Pp.runs(c, Pp.Wr{}, auto, ans) == True{} : Bool}, no: {Pp.Ans.yes(ans) == False{} : Bool}) -> {Pp.Cls.secret(c) == False{} : Bool}:
  match c:
    case Pp.Inside{}:
      {==}
    case Pp.Outside{}:
      {==}
    case Pp.Protected{}:
      {==}
    case Pp.Secret{}:
      pp.yes_clash({True{} == False{} : Bool}, ans, ran, no)

# 5. The spec
# -----------

# ids.eq is the spec's pp_same
def pp.ids_same(xs: List<&2, Nat>, ys: List<&2, Nat>) -> {Tl.ids.eq(xs, ys) == PathPolicy.pp_same(xs, ys) : Bool}:
  match xs:
    case Nil{}:
      match ys:
        case Nil{}:
          {==}
        case y <> yr:
          {==}
    case +x <> xr:
      match ys:
        case Nil{}:
          {==}
        case +y <> yr:
          %pp.ids_same(xr, yr) : {Bool.and(Nat.is_eq(x, y), Tl.ids.eq(xr, yr)) == Bool.and(Nat.is_eq(x, y), _) : Bool}
          {==}

# the class picked is a secret exactly when the secret test holds
def pp.pick_secret(s: Bool, p: Bool, i: Bool) -> {Pp.Cls.secret(Pp.cls.pick(s, p, i)) == s : Bool}:
  match s:
    case True{}:
      {==}
    case False{}:
      match p:
        case True{}:
          {==}
        case False{}:
          match i:
            case True{}:
              {==}
            case False{}:
              {==}

# the class of a real path is a secret exactly when the model's secret
# test holds
def pp.class_of_secret(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> {Pp.Cls.secret(Pp.class_of(Pp.Pol{ro, ru, se}, at)) == Pp.any_under(se, at) : Bool}:
  pp.pick_secret(Pp.any_under(se, at), Pp.protects(Pp.Pol{ro, ru, se}, at), Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(ro, at)))

# 6. The entry, spelled
# ---------------------

# the entry's rule writer is the spec's
def pp.rule_eq(r: Pp.Rule) -> {FPp.rule(r) == PathPolicy.pp_rule(r) : List<&2, Nat>}:
  match r:
    case Pp.Tree{p}:
      {==}
    case Pp.Dir{p}:
      {==}
    case Pp.Named{n}:
      {==}

def pp.rules_eq(rs: List<&2, Pp.Rule>) -> {FPp.rules(rs) == PathPolicy.pp_rules(rs) : List<&2, List<&2, Nat>>}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      %pp.rule_eq(r) : {FPp.rule(r) <> FPp.rules(rest) == _ <> PathPolicy.pp_rules(rest) : List<&2, List<&2, Nat>>}
      %pp.rules_eq(rest) : {FPp.rule(r) <> FPp.rules(rest) == FPp.rule(r) <> _ : List<&2, List<&2, Nat>>}
      {==}

# the flat writer is the spec's
def pp.one_eq(xs: List<&2, Nat>, +rest: List<&2, Nat>) -> {Fl.one(xs, rest) == PathPolicy.pp_flat_one(xs, rest) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => {1n+x : Nat} <> z, Fl.one(t, rest), PathPolicy.pp_flat_one(t, rest), pp.one_eq(t, rest))

def pp.flat_eq(xss: List<&2, List<&2, Nat>>) -> {Fl.flat(xss) == PathPolicy.pp_flat(xss) : List<&2, Nat>}:
  match xss:
    case Nil{}:
      {==}
    case +xs <> +t:
      %pp.flat_eq(t) : {Fl.one(xs, Fl.flat(t)) == PathPolicy.pp_flat_one(xs, _) : List<&2, Nat>}
      pp.one_eq(xs, Fl.flat(t))

def pp.flat_rules_eq(+ru: List<&2, Pp.Rule>) -> {Fl.flat(FPp.rules(ru)) == PathPolicy.pp_flat(PathPolicy.pp_rules(ru)) : List<&2, Nat>}:
  %pp.rules_eq(ru) : {Fl.flat(FPp.rules(ru)) == PathPolicy.pp_flat(_) : List<&2, Nat>}
  pp.flat_eq(FPp.rules(ru))

# the entry's request writer is the spec's spelling
def pp.req_spell(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, +l: Bool, +rest: String) -> {FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest) == PathPolicy.pp_spell_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest) : String}:
  %pp.flat_eq(ro) : {FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest) == LawsBase.wire_spell_nats(_, LawsBase.wire_spell_nats(PathPolicy.pp_flat(PathPolicy.pp_rules(ru)), LawsBase.wire_spell_nats(PathPolicy.pp_flat(se), LawsBase.wire_spell_nats(at, Wr.put_bool(l, rest))))) : String}
  %pp.flat_rules_eq(ru) : {FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest) == LawsBase.wire_spell_nats(Fl.flat(ro), LawsBase.wire_spell_nats(_, LawsBase.wire_spell_nats(PathPolicy.pp_flat(se), LawsBase.wire_spell_nats(at, Wr.put_bool(l, rest))))) : String}
  %pp.flat_eq(se) : {FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest) == LawsBase.wire_spell_nats(Fl.flat(ro), LawsBase.wire_spell_nats(Fl.flat(FPp.rules(ru)), LawsBase.wire_spell_nats(_, LawsBase.wire_spell_nats(at, Wr.put_bool(l, rest))))) : String}
  %Wire.wire_nats_spells(at, Wr.put_bool(l, rest)) : {FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest) == LawsBase.wire_spell_nats(Fl.flat(ro), LawsBase.wire_spell_nats(Fl.flat(FPp.rules(ru)), LawsBase.wire_spell_nats(Fl.flat(se), _))) : String}
  %Wire.wire_nats_spells(Fl.flat(se), FPp.put_ns(at, Wr.put_bool(l, rest))) : {FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest) == LawsBase.wire_spell_nats(Fl.flat(ro), LawsBase.wire_spell_nats(Fl.flat(FPp.rules(ru)), _)) : String}
  %Wire.wire_nats_spells(Fl.flat(FPp.rules(ru)), FPp.put_ns(Fl.flat(se), FPp.put_ns(at, Wr.put_bool(l, rest)))) : {FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest) == LawsBase.wire_spell_nats(Fl.flat(ro), _) : String}
  %Wire.wire_nats_spells(Fl.flat(ro), FPp.put_ns(Fl.flat(FPp.rules(ru)), FPp.put_ns(Fl.flat(se), FPp.put_ns(at, Wr.put_bool(l, rest))))) : {FPp.put_req(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}, rest) == _ : String}
  {==}

# a spelled request that fits fits as the entry's own laws ask
def pp.fits_code(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, -l: Bool, hf: {PathPolicy.pp_req_fits(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) == True{} : Bool}) -> {Bool.and(Bool.and(Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Fl.flat(ro))), LawsBase.wire_nats_fit(Fl.flat(ro))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Fl.flat(FPp.rules(ru)))), LawsBase.wire_nats_fit(Fl.flat(FPp.rules(ru))))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, Fl.flat(se))), LawsBase.wire_nats_fit(Fl.flat(se)))), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, at)), LawsBase.wire_nats_fit(at))) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, Fl.flat(ro), PathPolicy.pp_flat(ro), pp.flat_eq(ro)) : {Bool.and(Bool.and(Bool.and(PathPolicy.pp_nats_fit(_), PathPolicy.pp_nats_fit(Fl.flat(FPp.rules(ru)))), PathPolicy.pp_nats_fit(Fl.flat(se))), PathPolicy.pp_nats_fit(at)) == True{} : Bool}
  %Equal.sym(List<&2, Nat>, Fl.flat(FPp.rules(ru)), PathPolicy.pp_flat(PathPolicy.pp_rules(ru)), pp.flat_rules_eq(ru)) : {Bool.and(Bool.and(Bool.and(PathPolicy.pp_nats_fit(PathPolicy.pp_flat(ro)), PathPolicy.pp_nats_fit(_)), PathPolicy.pp_nats_fit(Fl.flat(se))), PathPolicy.pp_nats_fit(at)) == True{} : Bool}
  %Equal.sym(List<&2, Nat>, Fl.flat(se), PathPolicy.pp_flat(se), pp.flat_eq(se)) : {Bool.and(Bool.and(Bool.and(PathPolicy.pp_nats_fit(PathPolicy.pp_flat(ro)), PathPolicy.pp_nats_fit(PathPolicy.pp_flat(PathPolicy.pp_rules(ru)))), PathPolicy.pp_nats_fit(_)), PathPolicy.pp_nats_fit(at)) == True{} : Bool}
  hf

# the entry's class tags are Rust's
def pp.cls_eq(c: Pp.Cls) -> {FPp.cls(c) == PathPolicy.pp_cls_tag(c) : Nat}:
  match c:
    case Pp.Inside{}:
      {==}
    case Pp.Outside{}:
      {==}
    case Pp.Protected{}:
      {==}
    case Pp.Secret{}:
      {==}

# the entry's reply to the model's judgment is the spec's spelled answer
def pp.reply_spec(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>, +l: Bool) -> {FPp.put_judged(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l}), "") == PathPolicy.pp_spell_answer(FPp.Req{Pp.Pol{ro, ru, se}, Pp.Res{at, l}}) : String}:
  %pp.cls_eq(Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l}))) : {FPp.put_judged(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l}), "") == Wr.put_nat(_, Wr.put_bool(Pp.Judged.holds(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l})), "")) : String}
  {==}
