# eukhe: lemmas of area slash_args: the entry's reply encoders are the
# spec spellers of laws/slash_args/entry.bend (case by case on the answer;
# a list of words by wire_strs_spells), every reply opens with a Nat (never
# 'E'), and a decoded request is a spelled one (dcw.nat, dcw.str)

import Base
import ../../../bend/slash_args.bend as Sa
import ../../../bend/ffi_slash_args.bend as FSa
import ../../../bend/wire.bend as Wr
import ../../../laws/base.bend as LawsBase
import ../../../laws/wire.bend as Wire
import ../../../laws/slash_args/model.bend as SlashArgs
import ../../../laws/slash_args/entry.bend as SlashArgsEntry
import ../../wire/wire_strs_spells.bend as PWireStrsSpells
import ../../wire/wire_nat_exact.bend as PWireNatExact
import ../../base/wire_dec.bend as LE
import ../../base/staging.bend as LStg

# Encoders
# --------

def sae.mstr(m: Maybe<&2, String>, rest: String) -> {FSa.put_mstr(m, rest) == SlashArgsEntry.sae_mstr(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def sae.goal(g: Sa.Goal) -> {FSa.put_goal(g) == SlashArgsEntry.sae_goal(g) : String}:
  match g:
    case Sa.GStatus{}:
      {==}
    case Sa.GClear{}:
      {==}
    case Sa.GPause{}:
      {==}
    case Sa.GResume{}:
      {==}
    case Sa.GStart{+o, +b}:
      %Equal.sym(String, FSa.put_mstr(b, ""), SlashArgsEntry.sae_mstr(b, ""), sae.mstr(b, "")) : {Wr.put_nat(4n, Wr.put_str(o, _)) == Wr.put_nat(4n, Wr.put_str(o, SlashArgsEntry.sae_mstr(b, ""))) : String}
      {==}
    case Sa.GErr{e}:
      {==}

def sae.lim(m: Maybe<&2, Sa.Lim>, rest: String) -> {FSa.put_mlim(m, rest) == SlashArgsEntry.sae_lim(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{l}:
      match l:
        case Sa.LUnl{}:
          {==}
        case Sa.LNum{d}:
          {==}

def sae.cmds(m: Maybe<&2, List<&2, String>>, +rest: String) -> {FSa.put_mcmds(m, rest) == SlashArgsEntry.sae_cmds(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{+cs}:
      %Wire.wire_strs_spells(cs, rest) : {Wr.put_nat(1n, Wr.put_list(~String, ~Wr.put_str, cs, rest)) == Wr.put_nat(1n, _) : String}
      {==}

def sae.gates(m: Maybe<&2, Sa.Gates>, +rest: String) -> {FSa.put_mgates(m, rest) == SlashArgsEntry.sae_gates(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{g}:
      match g:
        case Sa.Gates{+cs, +r, +t}:
          %Equal.sym(String, FSa.put_mstr(t, rest), SlashArgsEntry.sae_mstr(t, rest), sae.mstr(t, rest)) : {Wr.put_nat(1n, FSa.put_mcmds(cs, FSa.put_mstr(r, _))) == SlashArgsEntry.sae_gates(Some{Sa.Gates{cs, r, t}}, rest) : String}
          %Equal.sym(String, FSa.put_mstr(r, SlashArgsEntry.sae_mstr(t, rest)), SlashArgsEntry.sae_mstr(r, SlashArgsEntry.sae_mstr(t, rest)), sae.mstr(r, SlashArgsEntry.sae_mstr(t, rest))) : {Wr.put_nat(1n, FSa.put_mcmds(cs, _)) == SlashArgsEntry.sae_gates(Some{Sa.Gates{cs, r, t}}, rest) : String}
          %Equal.sym(String, FSa.put_mcmds(cs, SlashArgsEntry.sae_mstr(r, SlashArgsEntry.sae_mstr(t, rest))), SlashArgsEntry.sae_cmds(cs, SlashArgsEntry.sae_mstr(r, SlashArgsEntry.sae_mstr(t, rest))), sae.cmds(cs, SlashArgsEntry.sae_mstr(r, SlashArgsEntry.sae_mstr(t, rest)))) : {Wr.put_nat(1n, _) == SlashArgsEntry.sae_gates(Some{Sa.Gates{cs, r, t}}, rest) : String}
          {==}

def sae.conf(c: Sa.Conf) -> {FSa.put_conf(c) == SlashArgsEntry.sae_conf(c) : String}:
  match c:
    case Sa.Conf{+a, +b, +k, +m, +g, +p}:
      %Equal.sym(String, FSa.put_mstr(p, ""), SlashArgsEntry.sae_mstr(p, ""), sae.mstr(p, "")) : {FSa.put_mlim(a, FSa.put_mlim(b, FSa.put_mlim(k, FSa.put_mlim(m, FSa.put_mgates(g, _))))) == SlashArgsEntry.sae_conf(Sa.Conf{a, b, k, m, g, p}) : String}
      +x0 = SlashArgsEntry.sae_mstr(p, "")
      %Equal.sym(String, FSa.put_mgates(g, x0), SlashArgsEntry.sae_gates(g, x0), sae.gates(g, x0)) : {FSa.put_mlim(a, FSa.put_mlim(b, FSa.put_mlim(k, FSa.put_mlim(m, _)))) == SlashArgsEntry.sae_conf(Sa.Conf{a, b, k, m, g, p}) : String}
      +x1 = SlashArgsEntry.sae_gates(g, x0)
      %Equal.sym(String, FSa.put_mlim(m, x1), SlashArgsEntry.sae_lim(m, x1), sae.lim(m, x1)) : {FSa.put_mlim(a, FSa.put_mlim(b, FSa.put_mlim(k, _))) == SlashArgsEntry.sae_conf(Sa.Conf{a, b, k, m, g, p}) : String}
      +x2 = SlashArgsEntry.sae_lim(m, x1)
      %Equal.sym(String, FSa.put_mlim(k, x2), SlashArgsEntry.sae_lim(k, x2), sae.lim(k, x2)) : {FSa.put_mlim(a, FSa.put_mlim(b, _)) == SlashArgsEntry.sae_conf(Sa.Conf{a, b, k, m, g, p}) : String}
      +x3 = SlashArgsEntry.sae_lim(k, x2)
      %Equal.sym(String, FSa.put_mlim(b, x3), SlashArgsEntry.sae_lim(b, x3), sae.lim(b, x3)) : {FSa.put_mlim(a, _) == SlashArgsEntry.sae_conf(Sa.Conf{a, b, k, m, g, p}) : String}
      +x4 = SlashArgsEntry.sae_lim(b, x3)
      sae.lim(a, x4)

def sae.auto(a: Sa.Auto) -> {FSa.put_auto(a) == SlashArgsEntry.sae_auto(a) : String}:
  match a:
    case Sa.AStatus{}:
      {==}
    case Sa.AOn{+c}:
      %Equal.sym(String, FSa.put_conf(c), SlashArgsEntry.sae_conf(c), sae.conf(c)) : {Wr.put_nat(1n, _) == Wr.put_nat(1n, SlashArgsEntry.sae_conf(c)) : String}
      {==}
    case Sa.AOff{}:
      {==}
    case Sa.AErr{e}:
      {==}

# Replies never open with 'E'
# ---------------------------

def sae.goal_ok(g: Sa.Goal) -> {LawsBase.wire_opens_err(FSa.put_goal(g)) == False{} : Bool}:
  match g:
    case Sa.GStatus{}:
      {==}
    case Sa.GClear{}:
      {==}
    case Sa.GPause{}:
      {==}
    case Sa.GResume{}:
      {==}
    case Sa.GStart{o, b}:
      {==}
    case Sa.GErr{e}:
      {==}

def sae.auto_ok(a: Sa.Auto) -> {LawsBase.wire_opens_err(FSa.put_auto(a)) == False{} : Bool}:
  match a:
    case Sa.AStatus{}:
      {==}
    case Sa.AOn{c}:
      {==}
    case Sa.AOff{}:
      {==}
    case Sa.AErr{e}:
      {==}

def sae.answer_ok(q: FSa.Req) -> {LawsBase.wire_opens_err(FSa.answer(q)) == False{} : Bool}:
  match q:
    case FSa.QGoal{a}:
      sae.goal_ok(Sa.goal(a))
    case FSa.QAuto{a}:
      sae.auto_ok(Sa.auto(a))
    case FSa.QWords{a}:
      LE.dcw.fin_ok(Wr.put_list.go(~String, ~Wr.put_str, Sa.words(a), ""))
    case FSa.QObjective{a}:
      sae.goal_ok(Sa.goal.objective(a, None{}))

# Decoded requests are spelled
# ----------------------------

def sax.T(s: String) -> Type:
  Sigma<&1, &1, FSa.Req, q => {s == SlashArgsEntry.sae_req(q, "") : String} & {SlashArgsEntry.sae_fits(q) == True{} : Bool}>

def sax.goal(-s: String, -s1: String, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d), es: {s == Wr.put_nat(0n, s1) : String}, ok: {LawsBase.wire_opens_err(FSa.ffi.got(FSa.get_goal(d))) == False{} : Bool}) -> sax.T(s):
  match d:
    case Wr.Got{+a, rest}:
      match rest:
        case SNil{}:
          (e1, fit) = sp
          (FSa.QGoal{a}, (LE.dcw.after(s, 0n, s1, Wr.put_str(a, ""), es, e1), fit))
        case SCon{x, y}:
          LStg.stg.absurd(sax.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(sax.T(s), ok)

def sax.auto(-s: String, -s1: String, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d), es: {s == Wr.put_nat(1n, s1) : String}, ok: {LawsBase.wire_opens_err(FSa.ffi.got(FSa.get_auto(d))) == False{} : Bool}) -> sax.T(s):
  match d:
    case Wr.Got{+a, rest}:
      match rest:
        case SNil{}:
          (e1, fit) = sp
          (FSa.QAuto{a}, (LE.dcw.after(s, 1n, s1, Wr.put_str(a, ""), es, e1), fit))
        case SCon{x, y}:
          LStg.stg.absurd(sax.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(sax.T(s), ok)

def sax.words(-s: String, -s1: String, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d), es: {s == Wr.put_nat(2n, s1) : String}, ok: {LawsBase.wire_opens_err(FSa.ffi.got(FSa.get_words(d))) == False{} : Bool}) -> sax.T(s):
  match d:
    case Wr.Got{+a, rest}:
      match rest:
        case SNil{}:
          (e1, fit) = sp
          (FSa.QWords{a}, (LE.dcw.after(s, 2n, s1, Wr.put_str(a, ""), es, e1), fit))
        case SCon{x, y}:
          LStg.stg.absurd(sax.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(sax.T(s), ok)

def sax.obj(-s: String, -s1: String, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d), es: {s == Wr.put_nat(3n, s1) : String}, ok: {LawsBase.wire_opens_err(FSa.ffi.got(FSa.get_objective(d))) == False{} : Bool}) -> sax.T(s):
  match d:
    case Wr.Got{+a, rest}:
      match rest:
        case SNil{}:
          (e1, fit) = sp
          (FSa.QObjective{a}, (LE.dcw.after(s, 3n, s1, Wr.put_str(a, ""), es, e1), fit))
        case SCon{x, y}:
          LStg.stg.absurd(sax.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(sax.T(s), ok)

# a reply that is no error comes from a spelled request
def sax.top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSa.ffi.got(FSa.get_req.start(d))) == False{} : Bool}) -> sax.T(s):
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          sax.goal(s, s1, Wr.get_str(s1), LE.dcw.str(s1), Wire.wire_nat_exact(s, 0n, s1, ed), ok)
        case 1n:
          sax.auto(s, s1, Wr.get_str(s1), LE.dcw.str(s1), Wire.wire_nat_exact(s, 1n, s1, ed), ok)
        case 2n:
          sax.words(s, s1, Wr.get_str(s1), LE.dcw.str(s1), Wire.wire_nat_exact(s, 2n, s1, ed), ok)
        case 3n:
          sax.obj(s, s1, Wr.get_str(s1), LE.dcw.str(s1), Wire.wire_nat_exact(s, 3n, s1, ed), ok)
        case 4n+u:
          LStg.stg.absurd(sax.T(s), ok)
    case Wr.Bad{}:
      LStg.stg.absurd(sax.T(s), ok)
