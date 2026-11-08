# eukhe: the proof of LAW tiny_ffi_answers_spelled
#
# PROOF: the spec's spelling of a request is the entry's put_req
# (wire_nats_spells), so tiny_ffi_answers answers it with put_pick of the
# pick, which is the spec's spelling of the pick (tas.pick, tag by tag).

import Base
import ../../bend/ffi_tiny.bend as FTn
import ../../bend/tiny.bend as Tn
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tiny/pick.bend as Tiny
import ../../laws/wire.bend as Wire
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ./tiny_ffi_answers.bend as PTinyFfiAnswers

# the entry's reply to a pick is the spec's spelling of it
def tas.pick(p: Tn.Pick) -> {FTn.put_pick(p, "") == Tiny.tiny_spell_pick(p) : String}:
  match p:
    case Tn.Use{m}:
      {==}
    case Tn.Unavailable{}:
      {==}

# the spec's spelling of a request is the entry's
def tas.req(+c: List<&2, Nat>, +u: List<&2, Nat>, +rest: String) -> {FTn.put_req(FTn.Req{c, u}, rest) == Tiny.tiny_spell_req(FTn.Req{c, u}, rest) : String}:
  %Wire.wire_nats_spells(u, rest) : {FTn.put_req(FTn.Req{c, u}, rest) == LawsBase.wire_spell_nats(c, _) : String}
  Wire.wire_nats_spells(c, FTn.put_ids(u, rest))

def tas.main(q: FTn.Req, fits: {Tiny.tiny_req_fits(q) == True{} : Bool}) -> {FTn.ffi(Tiny.tiny_spell_req(q, "")) == Tiny.tiny_spell_answer(q) : String}:
  match q:
    case FTn.Req{+c, +u}:
      %tas.req(c, u, "") : {FTn.ffi(_) == Tiny.tiny_spell_pick(Tn.pick(c, u)) : String}
      Equal.trans(String, FTn.ffi(FTn.put_req(FTn.Req{c, u}, "")), FTn.put_pick(Tn.pick(c, u), ""), Tiny.tiny_spell_pick(Tn.pick(c, u)), Tiny.tiny_ffi_answers(c, u, fits), tas.pick(Tn.pick(c, u)))

def Tiny.tiny_ffi_answers_spelled(q, fits):
  tas.main(q, fits)
