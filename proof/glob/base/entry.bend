# eukhe: lemmas of the entry proofs of area glob (bend/ffi_glob.bend):
# a spelled request reads back (ge.req), the answer is the spelled spec
# answer (ge.reply), an answer never opens with 'E' (ge.answer_ok), and
# each decoder stage answers Got only for the spelling of what it read so
# far, every count and length within the wire (ge.x.*: the stage carries
# `pre`, the input spelled up to its field, and extends it with the
# field's exactness law).

import Base
import ../../../bend/glob.bend as G
import ../../../bend/ffi_glob.bend as FG
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/glob.bend as Glob
import ../../wire/wire_bool_round_trip.bend as PWireBoolRoundTrip
import ../../wire/wire_strs_round_trip.bend as PWireStrsRoundTrip
import ../../wire/wire_strs_spells.bend as PWireStrsSpells
import ../../wire/wire_nats_spells.bend as PWireNatsSpells
import ../../wire/wire_bool_exact.bend as PWireBoolExact
import ../../wire/wire_strs_exact.bend as PWireStrsExact
import ../../wire/wire_strs_decoded_fit.bend as PWireStrsDecodedFit
import ../../wire/wire_list_exact.bend as PWireListExact
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../wire/wire_nat_decoded_fits.bend as PWireNatDecodedFits
import ../../wire/wire_nat_not_err.bend as PWireNatNotErr
import ../../wire/wire_bool_not_err.bend as PWireBoolNotErr
import ../../base/wire.bend as LWire
import ../../base/logic/bool.bend as LLogicBool
import ../../base/bool.bend as LBool
import ../../base/staging.bend as LStg
import ../../base/wire_dec.bend as LE
import ../glob_groups.bend as PGlobGroups
import ../glob_allowed.bend as PGlobAllowed
import ../glob_rules.bend as PGlobRules
import ../glob_ignored.bend as PGlobIgnored

# Reading a spelled request
# -------------------------

def ge.req(q: FG.Req, +rest: String, h: {Glob.sp_fit_req(q) == True{} : Bool}) -> {FG.get_req(Glob.sp_w_req(q, rest)) == Wr.Got{q, rest} : Wr.Dec<FG.Req>}:
  match q:
    case FG.QCheck{+p}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(p, rest)), Wr.Got{p, rest}, Wire.wire_str_round_trip(p, rest, h)) : {FG.get_check(_) == Wr.Got{FG.QCheck{p}, rest} : Wr.Dec<FG.Req>}
      {==}
    case FG.QMatch{+sep, +fold, +ps, +ss, +ks}:
      +h1 = h
      +fps = LLogicBool.tree.pt.and_l(LawsBase.wire_strs_fit(ps), Bool.and(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks))), h1)
      +h2 = LLogicBool.tree.pt.and_r(LawsBase.wire_strs_fit(ps), Bool.and(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks))), h1)
      +fss = LLogicBool.tree.pt.and_l(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks)), h2)
      +fks = LLogicBool.tree.pt.and_r(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks)), h2)
      +r3 = LawsBase.wire_spell_nats(ks, rest)
      +r2 = LawsBase.wire_spell_strs(ss, r3)
      +r1 = LawsBase.wire_spell_strs(ps, r2)
      +r0 = Wr.put_bool(fold, r1)
      +goal = {Wr.Got{FG.QMatch{sep, fold, ps, ss, ks}, rest} : Wr.Dec<FG.Req>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(sep, r0)), Wr.Got{sep, r0}, Wire.wire_bool_round_trip(sep, r0)) : {FG.get_match(False{}, _) == goal : Wr.Dec<FG.Req>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r0), Wr.Got{fold, r1}, Wire.wire_bool_round_trip(fold, r1)) : {FG.get_match.fold(False{}, sep, _) == goal : Wr.Dec<FG.Req>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, r1), Wr.Got{ps, r2}, Wire.wire_strs_round_trip(ps, r2, fps)) : {FG.get_match.ps(False{}, sep, fold, _) == goal : Wr.Dec<FG.Req>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, r2), Wr.Got{ss, r3}, Wire.wire_strs_round_trip(ss, r3, fss)) : {FG.get_match.ss(False{}, sep, fold, ps, _) == goal : Wr.Dec<FG.Req>}
      %Wire.wire_nats_spells(ks, rest) : {FG.get_match.ks(False{}, sep, fold, ps, ss, Wr.get_list(~Nat, ~Wr.get_nat, _)) == goal : Wr.Dec<FG.Req>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, ks, rest)), Wr.Got{ks, rest}, Wire.wire_list_round_trip(ks, rest, fks)) : {FG.get_match.ks(False{}, sep, fold, ps, ss, _) == goal : Wr.Dec<FG.Req>}
      {==}
    case FG.QAllow{+sel, +ps}:
      +h1 = h
      +fsel = LLogicBool.tree.pt.and_l(LawsBase.wire_fits(String.length(sel)), LawsBase.wire_strs_fit(ps), h1)
      +fps = LLogicBool.tree.pt.and_r(LawsBase.wire_fits(String.length(sel)), LawsBase.wire_strs_fit(ps), h1)
      +r1 = LawsBase.wire_spell_strs(ps, rest)
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(sel, r1)), Wr.Got{sel, r1}, Wire.wire_str_round_trip(sel, r1, fsel)) : {FG.get_allow(_) == Wr.Got{FG.QAllow{sel, ps}, rest} : Wr.Dec<FG.Req>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, r1), Wr.Got{ps, rest}, Wire.wire_strs_round_trip(ps, rest, fps)) : {FG.get_allow.ps(sel, _) == Wr.Got{FG.QAllow{sel, ps}, rest} : Wr.Dec<FG.Req>}
      {==}
    case FG.QRules{+sep, +fold, +ps, +ss, +ks}:
      +h1 = h
      +fps = LLogicBool.tree.pt.and_l(LawsBase.wire_strs_fit(ps), Bool.and(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks))), h1)
      +h2 = LLogicBool.tree.pt.and_r(LawsBase.wire_strs_fit(ps), Bool.and(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks))), h1)
      +fss = LLogicBool.tree.pt.and_l(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks)), h2)
      +fks = LLogicBool.tree.pt.and_r(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks)), h2)
      +r3 = LawsBase.wire_spell_nats(ks, rest)
      +r2 = LawsBase.wire_spell_strs(ss, r3)
      +r1 = LawsBase.wire_spell_strs(ps, r2)
      +r0 = Wr.put_bool(fold, r1)
      +goal = {Wr.Got{FG.QRules{sep, fold, ps, ss, ks}, rest} : Wr.Dec<FG.Req>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(Wr.put_bool(sep, r0)), Wr.Got{sep, r0}, Wire.wire_bool_round_trip(sep, r0)) : {FG.get_match(True{}, _) == goal : Wr.Dec<FG.Req>}
      %Equal.sym(Wr.Dec<Bool>, Wr.get_bool(r0), Wr.Got{fold, r1}, Wire.wire_bool_round_trip(fold, r1)) : {FG.get_match.fold(True{}, sep, _) == goal : Wr.Dec<FG.Req>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, r1), Wr.Got{ps, r2}, Wire.wire_strs_round_trip(ps, r2, fps)) : {FG.get_match.ps(True{}, sep, fold, _) == goal : Wr.Dec<FG.Req>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, r2), Wr.Got{ss, r3}, Wire.wire_strs_round_trip(ss, r3, fss)) : {FG.get_match.ss(True{}, sep, fold, ps, _) == goal : Wr.Dec<FG.Req>}
      %Wire.wire_nats_spells(ks, rest) : {FG.get_match.ks(True{}, sep, fold, ps, ss, Wr.get_list(~Nat, ~Wr.get_nat, _)) == goal : Wr.Dec<FG.Req>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, ks, rest)), Wr.Got{ks, rest}, Wire.wire_list_round_trip(ks, rest, fks)) : {FG.get_match.ks(True{}, sep, fold, ps, ss, _) == goal : Wr.Dec<FG.Req>}
      {==}
    case FG.QIgnore{+ps, +cs, +es}:
      +h1 = h
      +fps = LLogicBool.tree.pt.and_l(LawsBase.wire_strs_fit(ps), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cs)), LawsBase.wire_nats_fit(cs)), LawsBase.wire_strs_fit(es)), h1)
      +h2 = LLogicBool.tree.pt.and_r(LawsBase.wire_strs_fit(ps), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cs)), LawsBase.wire_nats_fit(cs)), LawsBase.wire_strs_fit(es)), h1)
      +fcs = LLogicBool.tree.pt.and_l(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cs)), LawsBase.wire_nats_fit(cs)), LawsBase.wire_strs_fit(es), h2)
      +fes = LLogicBool.tree.pt.and_r(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cs)), LawsBase.wire_nats_fit(cs)), LawsBase.wire_strs_fit(es), h2)
      +r2 = LawsBase.wire_spell_strs(es, rest)
      +r1 = LawsBase.wire_spell_nats(cs, r2)
      +goal = {Wr.Got{FG.QIgnore{ps, cs, es}, rest} : Wr.Dec<FG.Req>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, LawsBase.wire_spell_strs(ps, r1)), Wr.Got{ps, r1}, Wire.wire_strs_round_trip(ps, r1, fps)) : {FG.get_ignore(_) == goal : Wr.Dec<FG.Req>}
      %Wire.wire_nats_spells(cs, r2) : {FG.get_ignore.cs(ps, Wr.get_list(~Nat, ~Wr.get_nat, _)) == goal : Wr.Dec<FG.Req>}
      %Equal.sym(Wr.Dec<List<&2, Nat>>, Wr.get_list(~Nat, ~Wr.get_nat, Wr.put_list(~Nat, ~Wr.put_nat, cs, r2)), Wr.Got{cs, r2}, Wire.wire_list_round_trip(cs, r2, fcs)) : {FG.get_ignore.cs(ps, _) == goal : Wr.Dec<FG.Req>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, r2), Wr.Got{es, rest}, Wire.wire_strs_round_trip(es, rest, fes)) : {FG.get_ignore.es(ps, cs, _) == goal : Wr.Dec<FG.Req>}
      {==}

# The answer
# ----------

def ge.err(e: G.Err) -> {FG.put_err(e, "") == Glob.sp_w_err(e) : String}:
  match e:
    case G.EClass{}:
      {==}
    case G.ERange{lo, hi}:
      match lo hi:
        case Chr{x} Chr{y}:
          {==}
    case G.EUnopened{}:
      {==}
    case G.EUnclosed{}:
      {==}
    case G.EEscape{}:
      {==}

def ge.check(r: Result<&2, &2, G.Err, G.Glob>) -> {FG.put_check(G.check.r(r)) == Glob.sp_w_check(r) : String}:
  match r:
    case Fail{+e}:
      %Equal.sym(String, FG.put_err(e, ""), Glob.sp_w_err(e), ge.err(e)) : {Wr.put_nat(1n, _) == Glob.sp_w_check(Fail{e}) : String}
      {==}
    case Done{g}:
      {==}

def ge.bools.go(xs: List<&2, Bool>) -> {Wr.put_list.go(~Bool, ~Wr.put_bool, xs, "") == (List.length(&2, Bool, xs), Glob.sp_w_bools.items(xs)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case +b <> +r:
      %Equal.sym(Nat & String, Wr.put_list.go(~Bool, ~Wr.put_bool, r, ""), (List.length(&2, Bool, r), Glob.sp_w_bools.items(r)), ge.bools.go(r)) : {Wr.put_list.step(~Bool, ~Wr.put_bool, b, _) == (List.length(&2, Bool, b <> r), Glob.sp_w_bools.items(b <> r)) : Nat & String}
      {==}

def ge.bools(+xs: List<&2, Bool>) -> {Wr.put_list(~Bool, ~Wr.put_bool, xs, "") == Glob.sp_w_bools(xs) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~Bool, ~Wr.put_bool, xs, ""), (List.length(&2, Bool, xs), Glob.sp_w_bools.items(xs)), ge.bools.go(xs)) : {Wr.put_list.fin(_) == Glob.sp_w_bools(xs) : String}
  {==}

# the entry's answer to a request is the spelled spec answer
def ge.reply(q: FG.Req) -> {FG.answer(q) == Glob.sp_w_reply(q) : String}:
  match q:
    case FG.QCheck{p}:
      ge.check(G.parse(p))
    case FG.QMatch{+sep, +fold, +ps, +ss, +ks}:
      +o = {G.Opts{sep, fold} : G.Opts}
      %Equal.sym(List<&2, Bool>, G.match_groups(o, ps, ss, ks), Glob.sp_groups(ks, Glob.sp_compile(o, ps), ss), Glob.glob_groups(o, ps, ss, ks)) : {Wr.put_list(~Bool, ~Wr.put_bool, _, "") == Glob.sp_w_reply(FG.QMatch{sep, fold, ps, ss, ks}) : String}
      ge.bools(Glob.sp_groups(ks, Glob.sp_compile(o, ps), ss))
    case FG.QAllow{+sel, +ps}:
      %Equal.sym(Bool, G.allowed(sel, ps), Glob.sp_allowed(sel, ps), Glob.glob_allowed(sel, ps)) : {Wr.put_bool(_, "") == Glob.sp_w_reply(FG.QAllow{sel, ps}) : String}
      {==}
    case FG.QRules{+sep, +fold, +ps, +ss, +ks}:
      +o = {G.Opts{sep, fold} : G.Opts}
      %Equal.sym(List<&2, Bool>, G.rules(ks, o, ps, ss), Glob.sp_rules(ks, o, ps, ss), Glob.glob_rules(ks, o, ps, ss)) : {Wr.put_list(~Bool, ~Wr.put_bool, _, "") == Glob.sp_w_reply(FG.QRules{sep, fold, ps, ss, ks}) : String}
      ge.bools(Glob.sp_rules(ks, o, ps, ss))
    case FG.QIgnore{+ps, +cs, +es}:
      %Equal.sym(List<&2, Bool>, G.ignored(ps, cs, es), Glob.sp_ignored(ps, cs, es), Glob.glob_ignored(ps, cs, es)) : {Wr.put_list(~Bool, ~Wr.put_bool, _, "") == Glob.sp_w_reply(FG.QIgnore{ps, cs, es}) : String}
      ge.bools(Glob.sp_ignored(ps, cs, es))

# Answers are values
# ------------------

def ge.check_ok(m: Maybe<&2, G.Err>) -> {LawsBase.wire_opens_err(FG.put_check(m)) == False{} : Bool}:
  match m:
    case None{}:
      Wire.wire_nat_not_err(0n, "")
    case Some{e}:
      Wire.wire_nat_not_err(1n, FG.put_err(e, ""))

def ge.answer_ok(q: FG.Req) -> {LawsBase.wire_opens_err(FG.answer(q)) == False{} : Bool}:
  match q:
    case FG.QCheck{p}:
      ge.check_ok(G.check(p))
    case FG.QMatch{sep, fold, ps, ss, ks}:
      LE.dcw.fin_ok(Wr.put_list.go(~Bool, ~Wr.put_bool, G.match_groups(G.Opts{sep, fold}, ps, ss, ks), ""))
    case FG.QAllow{sel, ps}:
      Wire.wire_bool_not_err(G.allowed(sel, ps), "")
    case FG.QRules{sep, fold, ps, ss, ks}:
      LE.dcw.fin_ok(Wr.put_list.go(~Bool, ~Wr.put_bool, G.rules(ks, G.Opts{sep, fold}, ps, ss), ""))
    case FG.QIgnore{ps, cs, es}:
      LE.dcw.fin_ok(Wr.put_list.go(~Bool, ~Wr.put_bool, G.ignored(ps, cs, es), ""))

# Exactness
# ---------

def ge.RP(s: String, d: Wr.Dec<FG.Req>) -> Type:
  match d:
    case Wr.Got{q, r}:
      {s == Glob.sp_w_req(q, r) : String} & {Glob.sp_fit_req(q) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a decoded list of Nats: its length and its items
def ge.GoP(m: Nat, d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {List.length(&2, Nat, xs) == 1n+m : Nat} & {LawsBase.wire_nats_fit(xs) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ge.go.cons(+m: Nat, +x: Nat, fx: {LawsBase.wire_fits(x) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, v: ge.GoP(m, d)) -> ge.GoP(1n+m, Wr.get_list.cons(Nat, x, d)):
  match d:
    case Wr.Got{+xs, r}:
      (e1, e2) = v
      (Equal.cong(Nat, Nat, z => 1n+z, List.length(&2, Nat, xs), 1n+m, e1), LBool.cb_and_intro(LawsBase.wire_fits(x), LawsBase.wire_nats_fit(xs), fx, e2))
    case Wr.Bad{}:
      Unit{}

def ge.go(m: Nat, +s: String, cur: Wr.Dec<Nat>, ec: {Wr.get_nat(s) == cur : Wr.Dec<Nat>}) -> ge.GoP(m, Wr.get_list.go(~Nat, ~Wr.get_nat, m, cur)):
  match m:
    case 0n:
      match cur:
        case Wr.Got{+x, +r}:
          ({==}, LBool.cb_and_intro(LawsBase.wire_fits(x), True{}, Wire.wire_nat_decoded_fits(s, x, r, ec), {==}))
        case Wr.Bad{}:
          Unit{}
    case 1n++k:
      match cur:
        case Wr.Got{+x, +r}:
          ge.go.cons(k, x, Wire.wire_nat_decoded_fits(s, x, r, ec), Wr.get_list.go(~Nat, ~Wr.get_nat, k, Wr.get_nat(r)), ge.go(k, r, Wr.get_nat(r), {==}))
        case Wr.Bad{}:
          Unit{}

def ge.NF(d: Wr.Dec<List<&2, Nat>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def ge.nf.go(+m: Nat, fn: {LawsBase.wire_fits(1n+m) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, v: ge.GoP(m, d)) -> ge.NF(d):
  match d:
    case Wr.Got{+xs, r}:
      (e1, e2) = v
      %Equal.sym(Nat, List.length(&2, Nat, xs), 1n+m, e1) : {Bool.and(LawsBase.wire_fits(_), LawsBase.wire_nats_fit(xs)) == True{} : Bool}
      LBool.cb_and_intro(LawsBase.wire_fits(1n+m), LawsBase.wire_nats_fit(xs), fn, e2)
    case Wr.Bad{}:
      Unit{}

def ge.nf.n(n: Nat, +s1: String, fn: {LawsBase.wire_fits(n) == True{} : Bool}) -> ge.NF(Wr.get_list.start(~Nat, ~Wr.get_nat, Wr.Got{n, s1})):
  match n:
    case 0n:
      {==}
    case 1n++m:
      ge.nf.go(m, fn, Wr.get_list.go(~Nat, ~Wr.get_nat, m, Wr.get_nat(s1)), ge.go(m, s1, Wr.get_nat(s1), {==}))

def ge.nf.start(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ge.NF(Wr.get_list.start(~Nat, ~Wr.get_nat, d)):
  match d:
    case Wr.Got{+n, +s1}:
      +fn = Wire.wire_nat_decoded_fits(s, n, s1, ed)
      ge.nf.n(n, s1, fn)
    case Wr.Bad{}:
      Unit{}

# a decoded list of Nats fits the wire: its count and every item
def ge.nats_fit(+s: String, +xs: List<&2, Nat>, +r: String, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s) == Wr.Got{xs, r} : Wr.Dec<List<&2, Nat>>}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, xs)), LawsBase.wire_nats_fit(xs)) == True{} : Bool}:
  %ed : ge.NF(_)
  ge.nf.start(s, Wr.get_nat(s), {==})

def ge.x.check(-s: String, +s0: String, pre: {s == Wr.put_nat(0n, s0) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s0, d)) -> ge.RP(s, FG.get_check(d)):
  match d:
    case Wr.Got{+p, +r}:
      (e, fp) = sp
      (Equal.trans(String, s, Wr.put_nat(0n, s0), Wr.put_nat(0n, Wr.put_str(p, r)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s0, Wr.put_str(p, r), e)), fp)
    case Wr.Bad{}:
      Unit{}

# the tag of the group query (rules False) or the rules query (rules True)
def ge.tg(rules: Bool) -> Nat:
  match rules:
    case True{}:
      3n
    case False{}:
      1n

# the spelling of a group or rules query before its sizes x
def ge.m(rules: Bool, sep: Bool, fold: Bool, ps: List<&2, String>, ss: List<&2, String>, x: String) -> String:
  Wr.put_nat(ge.tg(rules), Wr.put_bool(sep, Wr.put_bool(fold, LawsBase.wire_spell_strs(ps, LawsBase.wire_spell_strs(ss, x)))))

def ge.x.mk(rules: Bool, -s: String, -sep: Bool, -fold: Bool, -ps: List<&2, String>, -ss: List<&2, String>, -ks: List<&2, Nat>, -r: String, e: {s == ge.m(rules, sep, fold, ps, ss, LawsBase.wire_spell_nats(ks, r)) : String}, f: {Bool.and(LawsBase.wire_strs_fit(ps), Bool.and(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks)))) == True{} : Bool}) -> ge.RP(s, Wr.Got{FG.mkq(rules, sep, fold, ps, ss, ks), r}):
  match rules:
    case True{}:
      (e, f)
    case False{}:
      (e, f)

def ge.x.ks(+rules: Bool, -s: String, +sep: Bool, +fold: Bool, +ps: List<&2, String>, +ss: List<&2, String>, +s4: String, pre: {s == ge.m(rules, sep, fold, ps, ss, s4) : String}, fps: {LawsBase.wire_strs_fit(ps) == True{} : Bool}, fss: {LawsBase.wire_strs_fit(ss) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s4) == d : Wr.Dec<List<&2, Nat>>}) -> ge.RP(s, FG.get_match.ks(rules, sep, fold, ps, ss, d)):
  match d:
    case Wr.Got{+ks, +r}:
      +ee = ed
      +e0 = Wire.wire_list_exact(s4, ks, r, ee)
      +e = Equal.trans(String, s4, Wr.put_list(~Nat, ~Wr.put_nat, ks, r), LawsBase.wire_spell_nats(ks, r), e0, Wire.wire_nats_spells(ks, r))
      +fks = ge.nats_fit(s4, ks, r, ee)
      ge.x.mk(rules, s, sep, fold, ps, ss, ks, r, Equal.trans(String, s, ge.m(rules, sep, fold, ps, ss, s4), ge.m(rules, sep, fold, ps, ss, LawsBase.wire_spell_nats(ks, r)), pre, Equal.cong(String, String, z => ge.m(rules, sep, fold, ps, ss, z), s4, LawsBase.wire_spell_nats(ks, r), e)), LBool.cb_and_intro(LawsBase.wire_strs_fit(ps), Bool.and(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks))), fps, LBool.cb_and_intro(LawsBase.wire_strs_fit(ss), Bool.and(LawsBase.wire_fits(List.length(&2, Nat, ks)), LawsBase.wire_nats_fit(ks)), fss, fks)))
    case Wr.Bad{}:
      Unit{}

def ge.x.ss(+rules: Bool, -s: String, +sep: Bool, +fold: Bool, +ps: List<&2, String>, +s3: String, pre: {s == Wr.put_nat(ge.tg(rules), Wr.put_bool(sep, Wr.put_bool(fold, LawsBase.wire_spell_strs(ps, s3)))) : String}, fps: {LawsBase.wire_strs_fit(ps) == True{} : Bool}, d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s3) == d : Wr.Dec<List<&2, String>>}) -> ge.RP(s, FG.get_match.ss(rules, sep, fold, ps, d)):
  match d:
    case Wr.Got{+ss, +r}:
      +ee = ed
      +e = Wire.wire_strs_exact(s3, ss, r, ee)
      +fss = Wire.wire_strs_decoded_fit(s3, ss, r, ee)
      ge.x.ks(rules, s, sep, fold, ps, ss, r, Equal.trans(String, s, Wr.put_nat(ge.tg(rules), Wr.put_bool(sep, Wr.put_bool(fold, LawsBase.wire_spell_strs(ps, s3)))), ge.m(rules, sep, fold, ps, ss, r), pre, Equal.cong(String, String, z => Wr.put_nat(ge.tg(rules), Wr.put_bool(sep, Wr.put_bool(fold, LawsBase.wire_spell_strs(ps, z)))), s3, LawsBase.wire_spell_strs(ss, r), e)), fps, fss, Wr.get_list(~Nat, ~Wr.get_nat, r), {==})
    case Wr.Bad{}:
      Unit{}

def ge.x.ps(+rules: Bool, -s: String, +sep: Bool, +fold: Bool, +s2: String, pre: {s == Wr.put_nat(ge.tg(rules), Wr.put_bool(sep, Wr.put_bool(fold, s2))) : String}, d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s2) == d : Wr.Dec<List<&2, String>>}) -> ge.RP(s, FG.get_match.ps(rules, sep, fold, d)):
  match d:
    case Wr.Got{+ps, +r}:
      +ee = ed
      +e = Wire.wire_strs_exact(s2, ps, r, ee)
      +fps = Wire.wire_strs_decoded_fit(s2, ps, r, ee)
      ge.x.ss(rules, s, sep, fold, ps, r, Equal.trans(String, s, Wr.put_nat(ge.tg(rules), Wr.put_bool(sep, Wr.put_bool(fold, s2))), Wr.put_nat(ge.tg(rules), Wr.put_bool(sep, Wr.put_bool(fold, LawsBase.wire_spell_strs(ps, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(ge.tg(rules), Wr.put_bool(sep, Wr.put_bool(fold, z))), s2, LawsBase.wire_spell_strs(ps, r), e)), fps, Wr.get_list(~String, ~Wr.get_str, r), {==})
    case Wr.Bad{}:
      Unit{}

def ge.x.fold(+rules: Bool, -s: String, +sep: Bool, +s1: String, pre: {s == Wr.put_nat(ge.tg(rules), Wr.put_bool(sep, s1)) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s1) == d : Wr.Dec<Bool>}) -> ge.RP(s, FG.get_match.fold(rules, sep, d)):
  match d:
    case Wr.Got{+fold, +r}:
      +e = Wire.wire_bool_exact(s1, fold, r, ed)
      ge.x.ps(rules, s, sep, fold, r, Equal.trans(String, s, Wr.put_nat(ge.tg(rules), Wr.put_bool(sep, s1)), Wr.put_nat(ge.tg(rules), Wr.put_bool(sep, Wr.put_bool(fold, r))), pre, Equal.cong(String, String, z => Wr.put_nat(ge.tg(rules), Wr.put_bool(sep, z)), s1, Wr.put_bool(fold, r), e)), Wr.get_list(~String, ~Wr.get_str, r), {==})
    case Wr.Bad{}:
      Unit{}

def ge.x.sep(+rules: Bool, -s: String, +s0: String, pre: {s == Wr.put_nat(ge.tg(rules), s0) : String}, d: Wr.Dec<Bool>, ed: {Wr.get_bool(s0) == d : Wr.Dec<Bool>}) -> ge.RP(s, FG.get_match(rules, d)):
  match d:
    case Wr.Got{+sep, +r}:
      +e = Wire.wire_bool_exact(s0, sep, r, ed)
      ge.x.fold(rules, s, sep, r, Equal.trans(String, s, Wr.put_nat(ge.tg(rules), s0), Wr.put_nat(ge.tg(rules), Wr.put_bool(sep, r)), pre, Equal.cong(String, String, z => Wr.put_nat(ge.tg(rules), z), s0, Wr.put_bool(sep, r), e)), Wr.get_bool(r), {==})
    case Wr.Bad{}:
      Unit{}

def ge.x.i.es(-s: String, +ps: List<&2, String>, +cs: List<&2, Nat>, +s2: String, pre: {s == Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, LawsBase.wire_spell_nats(cs, s2))) : String}, fps: {LawsBase.wire_strs_fit(ps) == True{} : Bool}, fcs: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cs)), LawsBase.wire_nats_fit(cs)) == True{} : Bool}, d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s2) == d : Wr.Dec<List<&2, String>>}) -> ge.RP(s, FG.get_ignore.es(ps, cs, d)):
  match d:
    case Wr.Got{+es, +r}:
      +ee = ed
      +e = Wire.wire_strs_exact(s2, es, r, ee)
      +fes = Wire.wire_strs_decoded_fit(s2, es, r, ee)
      (Equal.trans(String, s, Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, LawsBase.wire_spell_nats(cs, s2))), Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, LawsBase.wire_spell_nats(cs, LawsBase.wire_spell_strs(es, r)))), pre, Equal.cong(String, String, z => Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, LawsBase.wire_spell_nats(cs, z))), s2, LawsBase.wire_spell_strs(es, r), e)), LBool.cb_and_intro(LawsBase.wire_strs_fit(ps), Bool.and(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cs)), LawsBase.wire_nats_fit(cs)), LawsBase.wire_strs_fit(es)), fps, LBool.cb_and_intro(Bool.and(LawsBase.wire_fits(List.length(&2, Nat, cs)), LawsBase.wire_nats_fit(cs)), LawsBase.wire_strs_fit(es), fcs, fes)))
    case Wr.Bad{}:
      Unit{}

def ge.x.i.cs(-s: String, +ps: List<&2, String>, +s1: String, pre: {s == Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, s1)) : String}, fps: {LawsBase.wire_strs_fit(ps) == True{} : Bool}, d: Wr.Dec<List<&2, Nat>>, ed: {Wr.get_list(~Nat, ~Wr.get_nat, s1) == d : Wr.Dec<List<&2, Nat>>}) -> ge.RP(s, FG.get_ignore.cs(ps, d)):
  match d:
    case Wr.Got{+cs, +r}:
      +ee = ed
      +e0 = Wire.wire_list_exact(s1, cs, r, ee)
      +e = Equal.trans(String, s1, Wr.put_list(~Nat, ~Wr.put_nat, cs, r), LawsBase.wire_spell_nats(cs, r), e0, Wire.wire_nats_spells(cs, r))
      +fcs = ge.nats_fit(s1, cs, r, ee)
      ge.x.i.es(s, ps, cs, r, Equal.trans(String, s, Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, s1)), Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, LawsBase.wire_spell_nats(cs, r))), pre, Equal.cong(String, String, z => Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, z)), s1, LawsBase.wire_spell_nats(cs, r), e)), fps, fcs, Wr.get_list(~String, ~Wr.get_str, r), {==})
    case Wr.Bad{}:
      Unit{}

def ge.x.i.ps(-s: String, +s0: String, pre: {s == Wr.put_nat(4n, s0) : String}, d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s0) == d : Wr.Dec<List<&2, String>>}) -> ge.RP(s, FG.get_ignore(d)):
  match d:
    case Wr.Got{+ps, +r}:
      +ee = ed
      +e = Wire.wire_strs_exact(s0, ps, r, ee)
      +fps = Wire.wire_strs_decoded_fit(s0, ps, r, ee)
      ge.x.i.cs(s, ps, r, Equal.trans(String, s, Wr.put_nat(4n, s0), Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, r)), pre, Equal.cong(String, String, z => Wr.put_nat(4n, z), s0, LawsBase.wire_spell_strs(ps, r), e)), fps, Wr.get_list(~Nat, ~Wr.get_nat, r), {==})
    case Wr.Bad{}:
      Unit{}

def ge.x.aps(-s: String, +sel: String, +s1: String, pre: {s == Wr.put_nat(2n, Wr.put_str(sel, s1)) : String}, fsel: {LawsBase.wire_fits(String.length(sel)) == True{} : Bool}, d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s1) == d : Wr.Dec<List<&2, String>>}) -> ge.RP(s, FG.get_allow.ps(sel, d)):
  match d:
    case Wr.Got{+ps, +r}:
      +ee = ed
      +e = Wire.wire_strs_exact(s1, ps, r, ee)
      +fps = Wire.wire_strs_decoded_fit(s1, ps, r, ee)
      (Equal.trans(String, s, Wr.put_nat(2n, Wr.put_str(sel, s1)), Wr.put_nat(2n, Wr.put_str(sel, LawsBase.wire_spell_strs(ps, r))), pre, Equal.cong(String, String, z => Wr.put_nat(2n, Wr.put_str(sel, z)), s1, LawsBase.wire_spell_strs(ps, r), e)), LBool.cb_and_intro(LawsBase.wire_fits(String.length(sel)), LawsBase.wire_strs_fit(ps), fsel, fps))
    case Wr.Bad{}:
      Unit{}

def ge.x.sel(-s: String, +s0: String, pre: {s == Wr.put_nat(2n, s0) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(s0, d)) -> ge.RP(s, FG.get_allow(d)):
  match d:
    case Wr.Got{+sel, +r}:
      (e, fsel) = sp
      ge.x.aps(s, sel, r, Equal.trans(String, s, Wr.put_nat(2n, s0), Wr.put_nat(2n, Wr.put_str(sel, r)), pre, Equal.cong(String, String, z => Wr.put_nat(2n, z), s0, Wr.put_str(sel, r), e)), fsel, Wr.get_list(~String, ~Wr.get_str, r), {==})
    case Wr.Bad{}:
      Unit{}

def ge.x.tag(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}) -> ge.RP(s, FG.get_req.tag(d)):
  match d:
    case Wr.Got{+t, +s0}:
      match t:
        case 0n:
          ge.x.check(s, s0, Wire.wire_nat_exact(s, 0n, s0, ed), Wr.get_str(s0), LE.dcw.str(s0))
        case 1n:
          ge.x.sep(False{}, s, s0, Wire.wire_nat_exact(s, 1n, s0, ed), Wr.get_bool(s0), {==})
        case 2n:
          ge.x.sel(s, s0, Wire.wire_nat_exact(s, 2n, s0, ed), Wr.get_str(s0), LE.dcw.str(s0))
        case 3n:
          ge.x.sep(True{}, s, s0, Wire.wire_nat_exact(s, 3n, s0, ed), Wr.get_bool(s0), {==})
        case 4n:
          ge.x.i.ps(s, s0, Wire.wire_nat_exact(s, 4n, s0, ed), Wr.get_list(~String, ~Wr.get_str, s0), {==})
        case 5n+k:
          Unit{}
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def ge.x.top(-s: String, d: Wr.Dec<FG.Req>, rp: ge.RP(s, d), ok: {LawsBase.wire_opens_err(FG.ffi.got(d)) == False{} : Bool}) -> Sigma<&1, &1, FG.Req, r => {s == Glob.sp_w_req(r, "") : String} & {Glob.sp_fit_req(r) == True{} : Bool}>:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          (q, rp)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, FG.Req, r2 => {s == Glob.sp_w_req(r2, "") : String} & {Glob.sp_fit_req(r2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, FG.Req, r2 => {s == Glob.sp_w_req(r2, "") : String} & {Glob.sp_fit_req(r2) == True{} : Bool}>, ok)

def ge.refuse(d: Wr.Dec<FG.Req>, bad: {LawsBase.wire_opens_err(FG.ffi.got(d)) == True{} : Bool}) -> {FG.ffi.got(d) == Wr.err("glob: malformed request") : String}:
  match d:
    case Wr.Got{+q, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FG.answer(q) == Wr.err("glob: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FG.answer(q)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FG.answer(q)), True{}, bad), ge.answer_ok(q)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}
