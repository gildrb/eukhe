# eukhe: the proof of LAW skill_ffi_refuses
#
# PROOF: the entry answers either a check (it opens with T or F:
# wire_bool_not_err), a description (it opens with its length:
# LE.dcw.sfin_ok), or the one error form; so an answer that opens with 'E'
# is that error form.

import Base
import ../../bend/ffi_skill_load.bend as FSk
import ../../bend/skill_load.bend as Sk
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/skill_load.bend as SkillLoad
import ../../laws/wire.bend as Wire
import ../base/staging.bend as LStg
import ../base/wire_dec.bend as LE
import ../wire/wire_bool_not_err.bend as PWireBoolNotErr

def sfr2.checked_ok(c: Sk.Checked) -> {LawsBase.wire_opens_err(FSk.put_checked(c)) == False{} : Bool}:
  match c:
    case Sk.Checked{l, n, ms}:
      Wire.wire_bool_not_err(l, Wr.put_str(n, FSk.put_strs(ms, "")))

def sfr2.answer_ok(a: Sk.Ask) -> {LawsBase.wire_opens_err(FSk.answer(a)) == False{} : Bool}:
  match a:
    case Sk.AskSkill{n, p, d}:
      sfr2.checked_ok(Sk.check(n, p, d))
    case Sk.AskTemplate{d, b}:
      LE.dcw.sfin_ok(Wr.put_str.go(Sk.summary(d, b), SNil{}, 0n), "")

def sfr2.refuse(d: Wr.Dec<Sk.Ask>, bad: {LawsBase.wire_opens_err(FSk.run(d)) == True{} : Bool}) -> {FSk.run(d) == Wr.err("skill_load: malformed request") : String}:
  match d:
    case Wr.Got{+a, rest}:
      match rest:
        case SNil{}:
          LStg.stg.absurd({FSk.answer(a) == Wr.err("skill_load: malformed request") : String}, Equal.trans(Bool, True{}, LawsBase.wire_opens_err(FSk.answer(a)), False{}, Equal.sym(Bool, LawsBase.wire_opens_err(FSk.answer(a)), True{}, bad), sfr2.answer_ok(a)))
        case SCon{x, y}:
          {==}
    case Wr.Bad{}:
      {==}

def SkillLoad.skill_ffi_refuses(s, bad):
  sfr2.refuse(FSk.get_ask(s), bad)
