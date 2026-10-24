# eukhe: the proof of LAW skill_ffi_answers
# The request's strings read back (LSk.sl.text_rt and the wire's string
# round trip); the replies are the laws' (LSk.sl.skill, LSk.sl.summary).

import Base
import ../../bend/ffi_skill_load.bend as FSk
import ../../bend/skill_load.bend as Sk
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/skill_load.bend as SkillLoad
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ./base.bend as LSk

def sfa.skill(+n: Maybe<&2, String>, +p: String, +d: Maybe<&2, String>, hn: {SkillLoad.text_fits(n) == True{} : Bool}, hp: {LawsBase.wire_fits(String.length(p)) == True{} : Bool}, hd: {SkillLoad.text_fits(d) == True{} : Bool}) -> {FSk.ffi(SkillLoad.spell_ask(Sk.AskSkill{n, p, d})) == SkillLoad.spell_answer(Sk.AskSkill{n, p, d}) : String}:
  %LSk.sl.text_rt(n, Wr.put_str(p, SkillLoad.spell_text(d, "")), hn) : {FSk.run(FSk.get_skill(_)) == SkillLoad.spell_answer(Sk.AskSkill{n, p, d}) : String}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(p, SkillLoad.spell_text(d, ""))), Wr.Got{p, SkillLoad.spell_text(d, "")}, Wire.wire_str_round_trip(p, SkillLoad.spell_text(d, ""), hp)) : {FSk.run(FSk.get_skill.parent(n, _)) == SkillLoad.spell_answer(Sk.AskSkill{n, p, d}) : String}
  %LSk.sl.text_rt(d, "", hd) : {FSk.run(FSk.get_skill.desc(n, p, _)) == SkillLoad.spell_answer(Sk.AskSkill{n, p, d}) : String}
  LSk.sl.skill(n, p, d)

def sfa.template(+d: Maybe<&2, String>, +b: String, hd: {SkillLoad.text_fits(d) == True{} : Bool}, hb: {LawsBase.wire_fits(String.length(b)) == True{} : Bool}) -> {FSk.ffi(SkillLoad.spell_ask(Sk.AskTemplate{d, b})) == SkillLoad.spell_answer(Sk.AskTemplate{d, b}) : String}:
  %LSk.sl.text_rt(d, Wr.put_str(b, ""), hd) : {FSk.run(FSk.get_template(_)) == SkillLoad.spell_answer(Sk.AskTemplate{d, b}) : String}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(b, "")), Wr.Got{b, ""}, Wire.wire_str_round_trip(b, "", hb)) : {FSk.run(FSk.get_template.body(d, _)) == SkillLoad.spell_answer(Sk.AskTemplate{d, b}) : String}
  %LSk.sl.summary(d, b) : {Wr.put_str(Sk.summary(d, b), "") == Wr.put_str(_, "") : String}
  {==}

def sfa.split(+a: Sk.Ask, +fits: {SkillLoad.ask_fits(a) == True{} : Bool}) -> {FSk.ffi(SkillLoad.spell_ask(a)) == SkillLoad.spell_answer(a) : String}:
  match a:
    case Sk.AskSkill{+n, +p, +d}:
      +hpd = LLogicBool.wr_and_r(SkillLoad.text_fits(n), Bool.and(LawsBase.wire_fits(String.length(p)), SkillLoad.text_fits(d)), fits)
      sfa.skill(n, p, d, LLogicBool.wr_and_l(SkillLoad.text_fits(n), Bool.and(LawsBase.wire_fits(String.length(p)), SkillLoad.text_fits(d)), fits), LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(p)), SkillLoad.text_fits(d), hpd), LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(p)), SkillLoad.text_fits(d), hpd))
    case Sk.AskTemplate{+d, +b}:
      sfa.template(d, b, LLogicBool.wr_and_l(SkillLoad.text_fits(d), LawsBase.wire_fits(String.length(b)), fits), LLogicBool.wr_and_r(SkillLoad.text_fits(d), LawsBase.wire_fits(String.length(b)), fits))

def SkillLoad.skill_ffi_answers(a, fits):
  sfa.split(a, fits)
