# eukhe: the proof of LAW cow_ffi_answers
# The entry answers a spelled request with the spelled plan of the model
# (cow_entry_answers_spelled), and the model's plan is the laws' rule over
# the laws' equality (LACow.cw.plan).

import Base
import ../../bend/ffi_sandbox.bend as FSb
import ../../bend/sandbox.bend as Sb
import ../../laws/base.bend as LawsBase
import ../../laws/sandbox.bend as Sandbox
import ../base/logic/bool.bend as LLogicBool
import ./base/cow.bend as LACow
import ./cow_entry_answers_spelled.bend as PCowEntryAnswersSpelled

def cowfa.go(+p: Maybe<&2, Nat>, +b: Maybe<&2, Nat>, +c: Maybe<&2, Nat>, +fits: {Sandbox.cow_req_fits(p, b, c) == True{} : Bool}) -> {FSb.ffi(Sandbox.cow_spell_req(p, b, c, "")) == Sandbox.cow_spell_plan(Sandbox.cow_plan_spec(p, b, c)) : String}:
  +hbc = LLogicBool.wr_and_r(LawsBase.wire_mfits(p), Bool.and(LawsBase.wire_mfits(b), LawsBase.wire_mfits(c)), fits)
  +hp = LLogicBool.wr_and_l(LawsBase.wire_mfits(p), Bool.and(LawsBase.wire_mfits(b), LawsBase.wire_mfits(c)), fits)
  +hb = LLogicBool.wr_and_l(LawsBase.wire_mfits(b), LawsBase.wire_mfits(c), hbc)
  +hc = LLogicBool.wr_and_r(LawsBase.wire_mfits(b), LawsBase.wire_mfits(c), hbc)
  %LACow.cw.plan(p, b, c) : {FSb.ffi(Sandbox.cow_spell_req(p, b, c, "")) == Sandbox.cow_spell_plan(_) : String}
  Sandbox.cow_entry_answers_spelled(p, b, c, hp, hb, hc)

def Sandbox.cow_ffi_answers(p, b, c, fits):
  cowfa.go(p, b, c, fits)
