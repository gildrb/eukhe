# eukhe: the proof of LAW skill_ffi_only_requests
#
# PROOF: each decoder of bend/ffi_skill_load.bend answers Got{x, rest}
# only for an input that is the laws' spelling of x before rest, with x
# within the wire (sfo.*: a predicate per decoder answer, carried stage by
# stage with the shared exactness lemmas LE.dcw.nat and LE.dcw.str). The
# entry answers a value only for a request read whole with nothing left:
# that input is the spelled request (sfo.top).

import Base
import ../../bend/ffi_skill_load.bend as FSk
import ../../bend/skill_load.bend as Sk
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/skill_load.bend as SkillLoad
import ../base/staging.bend as LStg
import ../base/bool.bend as LBool
import ../base/wire_dec.bend as LE

# a string that may be missing, read: it is spelled before what is left
def sfo.TP(s: String, d: Wr.Dec<Maybe<&2, String>>) -> Type:
  match d:
    case Wr.Got{m, r}:
      {s == SkillLoad.spell_text(m, r) : String} & {SkillLoad.text_fits(m) == True{} : Bool}
    case Wr.Bad{}:
      Unit

# a request read from s0: it is spelled before what is left
def sfo.AP(s0: String, d: Wr.Dec<Sk.Ask>) -> Type:
  match d:
    case Wr.Got{a, r}:
      {s0 == SkillLoad.spell_ask(a, r) : String} & {SkillLoad.ask_fits(a) == True{} : Bool}
    case Wr.Bad{}:
      Unit

def sfo.some(-s: String, -r: String, pre: {s == Wr.put_nat(1n, r) : String}, d: Wr.Dec<String>, sp: LE.dcw.SP(r, d)) -> sfo.TP(s, FSk.get_text.some(d)):
  match d:
    case Wr.Got{+x, +r2}:
      (e, f) = sp
      (LE.dcw.after(s, 1n, r, Wr.put_str(x, r2), pre, e), f)
    case Wr.Bad{}:
      Unit{}

def sfo.tag(-s: String, t: Nat, +r: String, pre: {s == Wr.put_nat(t, r) : String}) -> sfo.TP(s, FSk.get_text.tag(t, r)):
  match t:
    case 0n:
      (pre, {==})
    case 1n:
      sfo.some(s, r, pre, Wr.get_str(r), LE.dcw.str(r))
    case 2n+p:
      Unit{}

def sfo.text.at(-s: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s, d)) -> sfo.TP(s, FSk.get_text.go(d)):
  match d:
    case Wr.Got{+t, +r}:
      sfo.tag(s, t, r, np)
    case Wr.Bad{}:
      Unit{}

# a string that may be missing, read from s
def sfo.text(+s: String) -> sfo.TP(s, FSk.get_text(s)):
  sfo.text.at(s, Wr.get_nat(s), LE.dcw.nat(s))

def sfo.desc(-s0: String, +n: Maybe<&2, String>, +p: String, -s2: String, pre: {s0 == Wr.put_nat(0n, SkillLoad.spell_text(n, Wr.put_str(p, s2))) : String}, fn: {SkillLoad.text_fits(n) == True{} : Bool}, fp: {LawsBase.wire_fits(String.length(p)) == True{} : Bool}, d: Wr.Dec<Maybe<&2, String>>, tp: sfo.TP(s2, d)) -> sfo.AP(s0, FSk.get_skill.desc(n, p, d)):
  match d:
    case Wr.Got{+dd, +s3}:
      (e, fd) = tp
      (Equal.trans(String, s0, Wr.put_nat(0n, SkillLoad.spell_text(n, Wr.put_str(p, s2))), Wr.put_nat(0n, SkillLoad.spell_text(n, Wr.put_str(p, SkillLoad.spell_text(dd, s3)))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, SkillLoad.spell_text(n, Wr.put_str(p, z))), s2, SkillLoad.spell_text(dd, s3), e)),
        LBool.cb_and_intro(SkillLoad.text_fits(n), Bool.and(LawsBase.wire_fits(String.length(p)), SkillLoad.text_fits(dd)), fn, LBool.cb_and_intro(LawsBase.wire_fits(String.length(p)), SkillLoad.text_fits(dd), fp, fd)))
    case Wr.Bad{}:
      Unit{}

def sfo.parent(-s0: String, +n: Maybe<&2, String>, -s1: String, pre: {s0 == Wr.put_nat(0n, SkillLoad.spell_text(n, s1)) : String}, fn: {SkillLoad.text_fits(n) == True{} : Bool}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> sfo.AP(s0, FSk.get_skill.parent(n, d)):
  match d:
    case Wr.Got{+p, +s2}:
      (e, fp) = sp
      +pre2 = Equal.trans(String, s0, Wr.put_nat(0n, SkillLoad.spell_text(n, s1)), Wr.put_nat(0n, SkillLoad.spell_text(n, Wr.put_str(p, s2))), pre, Equal.cong(String, String, z => Wr.put_nat(0n, SkillLoad.spell_text(n, z)), s1, Wr.put_str(p, s2), e))
      sfo.desc(s0, n, p, s2, pre2, fn, fp, FSk.get_text(s2), sfo.text(s2))
    case Wr.Bad{}:
      Unit{}

def sfo.skill(-s0: String, -s: String, pre: {s0 == Wr.put_nat(0n, s) : String}, d: Wr.Dec<Maybe<&2, String>>, tp: sfo.TP(s, d)) -> sfo.AP(s0, FSk.get_skill(d)):
  match d:
    case Wr.Got{+n, +s1}:
      (e, fn) = tp
      +pre2 = Equal.trans(String, s0, Wr.put_nat(0n, s), Wr.put_nat(0n, SkillLoad.spell_text(n, s1)), pre, Equal.cong(String, String, z => Wr.put_nat(0n, z), s, SkillLoad.spell_text(n, s1), e))
      sfo.parent(s0, n, s1, pre2, fn, Wr.get_str(s1), LE.dcw.str(s1))
    case Wr.Bad{}:
      Unit{}

def sfo.body(-s0: String, +dd: Maybe<&2, String>, -s1: String, pre: {s0 == Wr.put_nat(1n, SkillLoad.spell_text(dd, s1)) : String}, fd: {SkillLoad.text_fits(dd) == True{} : Bool}, d: Wr.Dec<String>, sp: LE.dcw.SP(s1, d)) -> sfo.AP(s0, FSk.get_template.body(dd, d)):
  match d:
    case Wr.Got{+b, +s2}:
      (e, fb) = sp
      (Equal.trans(String, s0, Wr.put_nat(1n, SkillLoad.spell_text(dd, s1)), Wr.put_nat(1n, SkillLoad.spell_text(dd, Wr.put_str(b, s2))), pre, Equal.cong(String, String, z => Wr.put_nat(1n, SkillLoad.spell_text(dd, z)), s1, Wr.put_str(b, s2), e)),
        LBool.cb_and_intro(SkillLoad.text_fits(dd), LawsBase.wire_fits(String.length(b)), fd, fb))
    case Wr.Bad{}:
      Unit{}

def sfo.template(-s0: String, -s: String, pre: {s0 == Wr.put_nat(1n, s) : String}, d: Wr.Dec<Maybe<&2, String>>, tp: sfo.TP(s, d)) -> sfo.AP(s0, FSk.get_template(d)):
  match d:
    case Wr.Got{+dd, +s1}:
      (e, fd) = tp
      +pre2 = Equal.trans(String, s0, Wr.put_nat(1n, s), Wr.put_nat(1n, SkillLoad.spell_text(dd, s1)), pre, Equal.cong(String, String, z => Wr.put_nat(1n, z), s, SkillLoad.spell_text(dd, s1), e))
      sfo.body(s0, dd, s1, pre2, fd, Wr.get_str(s1), LE.dcw.str(s1))
    case Wr.Bad{}:
      Unit{}

def sfo.ask_tag(-s0: String, t: Nat, +s: String, pre: {s0 == Wr.put_nat(t, s) : String}) -> sfo.AP(s0, FSk.get_ask.tag(t, s)):
  match t:
    case 0n:
      sfo.skill(s0, s, pre, FSk.get_text(s), sfo.text(s))
    case 1n:
      sfo.template(s0, s, pre, FSk.get_text(s), sfo.text(s))
    case 2n+p:
      Unit{}

def sfo.ask(-s0: String, d: Wr.Dec<Nat>, np: LE.dcw.NP(s0, d)) -> sfo.AP(s0, FSk.get_ask.go(d)):
  match d:
    case Wr.Got{+t, +s}:
      sfo.ask_tag(s0, t, s, np)
    case Wr.Bad{}:
      Unit{}

# a value answered: a request read whole, nothing left
def sfo.top(-s: String, d: Wr.Dec<Sk.Ask>, ap: sfo.AP(s, d), ok: {LawsBase.wire_opens_err(FSk.run(d)) == False{} : Bool}) -> Sigma<&1, &1, Sk.Ask, a => {s == SkillLoad.spell_ask(a, "") : String} & {SkillLoad.ask_fits(a) == True{} : Bool}>:
  match d:
    case Wr.Got{+a, rest}:
      match rest:
        case SNil{}:
          (a, ap)
        case SCon{x, y}:
          LStg.stg.absurd(Sigma<&1, &1, Sk.Ask, a2 => {s == SkillLoad.spell_ask(a2, "") : String} & {SkillLoad.ask_fits(a2) == True{} : Bool}>, ok)
    case Wr.Bad{}:
      LStg.stg.absurd(Sigma<&1, &1, Sk.Ask, a2 => {s == SkillLoad.spell_ask(a2, "") : String} & {SkillLoad.ask_fits(a2) == True{} : Bool}>, ok)

def SkillLoad.skill_ffi_only_requests(s, ok):
  sfo.top(s, FSk.get_ask(s), sfo.ask(s, Wr.get_nat(s), LE.dcw.nat(s)), ok)
