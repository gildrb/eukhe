# eukhe: the proof of LAW skill_ffi_exact
# The entry reads every input as the laws' reader does (LSk.sl.ask); a
# whole request gets the entry's answer, which is the laws' on every
# request (LSk.sl.skill, LSk.sl.summary); anything else gets the error
# form.

import Base
import ../../bend/ffi_skill_load.bend as FSk
import ../../bend/skill_load.bend as Sk
import ../../bend/wire.bend as Wr
import ../../laws/skill_load.bend as SkillLoad
import ./base.bend as LSk

def sfe.answer(a: Sk.Ask) -> {FSk.answer(a) == SkillLoad.spell_answer(a) : String}:
  match a:
    case Sk.AskSkill{+n, +p, +d}:
      LSk.sl.skill(n, p, d)
    case Sk.AskTemplate{+d, +b}:
      %LSk.sl.summary(d, b) : {Wr.put_str(Sk.summary(d, b), "") == Wr.put_str(_, "") : String}
      {==}

def sfe.fin(b: Bool, a: Sk.Ask) -> {FSk.run.end(b, a) == SkillLoad.ffi_spec.read(SkillLoad.read_ask.end(b, a)) : String}:
  match b:
    case True{}:
      sfe.answer(a)
    case False{}:
      {==}

def sfe.whole(r: Wr.Dec<Sk.Ask>) -> {FSk.run(r) == SkillLoad.ffi_spec.read(SkillLoad.read_ask.whole(r)) : String}:
  match r:
    case Wr.Got{a, s}:
      sfe.fin(Wr.end(s), a)
    case Wr.Bad{}:
      {==}

def SkillLoad.skill_ffi_exact(s):
  %LSk.sl.ask(Wr.get_nat(s)) : {FSk.run(_) == SkillLoad.ffi_spec(s) : String}
  sfe.whole(SkillLoad.read_ask.go(Wr.get_nat(s)))
