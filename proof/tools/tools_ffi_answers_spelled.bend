# eukhe: the proof of LAW tools_ffi_answers_spelled
#
# PROOF: the entry's segment codes are the spec's (tas.codes), so the
# spec's spelling of a path is the entry's put_req (tas.req) and its fit
# the entry's (tas.fits); the entry answers it with put_names of
# Tl.resolve, the walk is the spec's reach (tas.walk, by induction on the
# segments) and put_names spells the names as the spec does (tas.names).

import Base
import ../../bend/ffi_tools.bend as FTl
import ../../bend/tools.bend as Tl
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/tools.bend as Tools
import ../../laws/wire.bend as Wire
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ./tools_ffi_request_round_trip.bend as PToolsFfiRequestRoundTrip

# the entry's segment codes are the spec's
def tas.code(g: Tl.Seg) -> {FTl.code(g) == Tools.tools_seg_code(g) : Nat}:
  match g:
    case Tl.Up{}:
      {==}
    case Tl.Here{}:
      {==}
    case Tl.Name{n}:
      {==}

def tas.codes(gs: List<&2, Tl.Seg>) -> {FTl.codes(gs) == Tools.tools_seg_codes(gs) : List<&2, Nat>}:
  match gs:
    case Nil{}:
      {==}
    case +g <> +rest:
      %tas.code(g) : {FTl.code(g) <> FTl.codes(rest) == _ <> Tools.tools_seg_codes(rest) : List<&2, Nat>}
      %tas.codes(rest) : {FTl.code(g) <> FTl.codes(rest) == FTl.code(g) <> _ : List<&2, Nat>}
      {==}

# the spec's spelling of a path is the entry's
def tas.req(+gs: List<&2, Tl.Seg>, +rest: String) -> {FTl.put_req(gs, rest) == Tools.tools_spell_req(gs, rest) : String}:
  Equal.trans(String, Wr.put_list(~Nat, ~Wr.put_nat, FTl.codes(gs), rest), Wr.put_list(~Nat, ~Wr.put_nat, Tools.tools_seg_codes(gs), rest), LawsBase.wire_spell_nats(Tools.tools_seg_codes(gs), rest), Equal.cong(List<&2, Nat>, String, z => Wr.put_list(~Nat, ~Wr.put_nat, z, rest), FTl.codes(gs), Tools.tools_seg_codes(gs), tas.codes(gs)), Wire.wire_nats_spells(Tools.tools_seg_codes(gs), rest))

# a path that fits as the spec says fits as the entry's laws ask
def tas.fits(+gs: List<&2, Tl.Seg>, fits: {Tools.tools_req_fits(gs) == True{} : Bool}) -> {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FTl.codes(gs))), LawsBase.wire_nats_fit(FTl.codes(gs))) == True{} : Bool}:
  %Equal.sym(List<&2, Nat>, FTl.codes(gs), Tools.tools_seg_codes(gs), tas.codes(gs)) : {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FTl.codes(gs))), LawsBase.wire_nats_fit(_)) == True{} : Bool}
  %Equal.sym(List<&2, Nat>, FTl.codes(gs), Tools.tools_seg_codes(gs), tas.codes(gs)) : {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, _)), LawsBase.wire_nats_fit(Tools.tools_seg_codes(gs))) == True{} : Bool}
  fits

# the reach from no names is no names
def tas.none(gs: List<&2, Tl.Seg>) -> {Tools.tools_reach(gs, None{}) == None{} : Maybe<&2, List<&2, Nat>>}:
  match gs:
    case Nil{}:
      {==}
    case g <> rest:
      tas.none(rest)

# the walk is the spec's reach
def tas.walk(gs: List<&2, Tl.Seg>, at: List<&2, Nat>) -> {Tl.walk(gs, at) == Tools.tools_reach(gs, Some{at}) : Maybe<&2, List<&2, Nat>>}:
  match gs:
    case Nil{}:
      {==}
    case g <> rest:
      match g:
        case Tl.Name{n}:
          tas.walk(rest, n <> at)
        case Tl.Here{}:
          tas.walk(rest, at)
        case Tl.Up{}:
          match at:
            case Nil{}:
              Equal.sym(Maybe<&2, List<&2, Nat>>, Tools.tools_reach(rest, None{}), None{}, tas.none(rest))
            case a <> above:
              tas.walk(rest, above)

# the entry spells the names as the spec does
def tas.names(m: Maybe<&2, List<&2, Nat>>) -> {FTl.put_names(m, "") == Tools.tools_spell_names(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{+xs}:
      %Wire.wire_nats_spells(xs, "") : {FTl.put_names(Some{xs}, "") == Wr.put_nat(1n, _) : String}
      {==}

# the entry's reply to a path read whole is the spec's answer
def tas.names_resolve(+gs: List<&2, Tl.Seg>) -> {FTl.put_names(Tl.resolve(gs), "") == Tools.tools_spell_answer(gs) : String}:
  %tas.walk(gs, Nil{}) : {FTl.put_names(Tl.walk(gs, Nil{}), "") == Tools.tools_spell_names(_) : String}
  tas.names(Tl.walk(gs, Nil{}))

# the entry reads its own spelling of a path back whole (the round trip)
# and answers put_names of Tl.resolve
def tas.answers(+gs: List<&2, Tl.Seg>, h: {Bool.and(LawsBase.wire_fits(List.length(&2, Nat, FTl.codes(gs))), LawsBase.wire_nats_fit(FTl.codes(gs))) == True{} : Bool}) -> {FTl.ffi(FTl.put_req(gs, "")) == FTl.put_names(Tl.resolve(gs), "") : String}:
  %Equal.sym(Wr.Dec<List<&2, Tl.Seg>>, FTl.get_req(FTl.put_req(gs, "")), Wr.Got{gs, ""}, Tools.tools_ffi_request_round_trip(gs, "", h)) : {FTl.answer(_) == FTl.put_names(Tl.resolve(gs), "") : String}
  {==}

def Tools.tools_ffi_answers_spelled(gs, fits):
  %tas.req(gs, "") : {FTl.ffi(_) == Tools.tools_spell_answer(gs) : String}
  Equal.trans(String, FTl.ffi(FTl.put_req(gs, "")), FTl.put_names(Tl.resolve(gs), ""), Tools.tools_spell_answer(gs), tas.answers(gs, tas.fits(gs, fits)), tas.names_resolve(gs))
