# eukhe: the proof of LAW skill_ffi_malformed_exact
# The entry reads every input as the laws' reader does; where that reader
# finds no whole request, the entry answers its error form.

import Base
import ../../bend/ffi_skill_load.bend as FSk
import ../../bend/skill_load.bend as Sk
import ../../bend/wire.bend as Wr
import ../../laws/skill_load.bend as SkillLoad
import ./base.bend as LSk

def sme.end(b: Bool, -a: Sk.Ask, no: {SkillLoad.read_ask.end(b, a) == None{} : Maybe<&2, Sk.Ask>}) -> {FSk.run.end(b, a) == SCon{'E', SCon{' ', "skill_load: malformed request"}} : String}:
  match b:
    case True{}:
      LSk.sl.some_none(Sk.Ask, a, {FSk.answer(a) == SCon{'E', SCon{' ', "skill_load: malformed request"}} : String}, no)
    case False{}:
      {==}

def sme.whole(r: Wr.Dec<Sk.Ask>, no: {SkillLoad.read_ask.whole(r) == None{} : Maybe<&2, Sk.Ask>}) -> {FSk.run(r) == SCon{'E', SCon{' ', "skill_load: malformed request"}} : String}:
  match r:
    case Wr.Got{a, s}:
      sme.end(Wr.end(s), a, no)
    case Wr.Bad{}:
      {==}

def SkillLoad.skill_ffi_malformed_exact(s, no):
  %LSk.sl.ask(Wr.get_nat(s)) : {FSk.run(_) == SCon{'E', SCon{' ', "skill_load: malformed request"}} : String}
  sme.whole(SkillLoad.read_ask.go(Wr.get_nat(s)), no)
