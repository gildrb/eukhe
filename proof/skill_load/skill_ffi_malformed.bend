# eukhe: the proof of LAW skill_ffi_malformed
# The entry reads every input as the laws' reader does (LSk.sl.ask); where
# that reader finds no whole request, the entry answers its error form.

import Base
import ../../bend/ffi_skill_load.bend as FSk
import ../../bend/skill_load.bend as Sk
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/skill_load.bend as SkillLoad
import ./base.bend as LSk

def sfm.end(b: Bool, -a: Sk.Ask, no: {SkillLoad.read_ask.end(b, a) == None{} : Maybe<&2, Sk.Ask>}) -> {LawsBase.wire_opens_err(FSk.run.end(b, a)) == True{} : Bool}:
  match b:
    case True{}:
      LSk.sl.some_none(Sk.Ask, a, {LawsBase.wire_opens_err(FSk.answer(a)) == True{} : Bool}, no)
    case False{}:
      {==}

def sfm.whole(r: Wr.Dec<Sk.Ask>, no: {SkillLoad.read_ask.whole(r) == None{} : Maybe<&2, Sk.Ask>}) -> {LawsBase.wire_opens_err(FSk.run(r)) == True{} : Bool}:
  match r:
    case Wr.Got{a, s}:
      sfm.end(Wr.end(s), a, no)
    case Wr.Bad{}:
      {==}

def SkillLoad.skill_ffi_malformed(s, no):
  %LSk.sl.ask(Wr.get_nat(s)) : {LawsBase.wire_opens_err(FSk.run(_)) == True{} : Bool}
  sfm.whole(SkillLoad.read_ask.go(Wr.get_nat(s)), no)
