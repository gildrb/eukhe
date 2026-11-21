# eukhe: the proof of LAW undo_entry_answers
#
# PROOF: the spelled request reads back whole with nothing left (LAR.unq.req), so the entry answers the model's decision, encoded as the spec spells it (una.reply: the answer codes are the spec's, each list of Nats by wire_nats_spells).

import Base
import ../../bend/undo.bend as U
import ../../bend/ffi_undo.bend as FU
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/undo.bend as Undo
import ./base.bend as LA
import ../../laws/wire.bend as Wire
import ../base/wire.bend as LWire
import ../wire/wire_nats_spells.bend as PWireNatsSpells
import ../base/logic/bool.bend as LLogicBool
import ./base/reads.bend as LAR
import ./undo_restores_rows.bend as PUndoRestoresRows

def una.fixes(fs: List<&2, U.Fix>) -> {FU.fix_codes(fs) == Undo.sp_w_fixes(fs) : List<&2, Nat>}:
  match fs:
    case Nil{}:
      {==}
    case Con{f, +t}:
      match f:
        case U.Keep{}:
          %Equal.sym(List<&2, Nat>, FU.fix_codes(t), Undo.sp_w_fixes(t), una.fixes(t)) : {0n <> _ == 0n <> Undo.sp_w_fixes(t) : List<&2, Nat>}
          {==}
        case U.Remove{}:
          %Equal.sym(List<&2, Nat>, FU.fix_codes(t), Undo.sp_w_fixes(t), una.fixes(t)) : {1n <> _ == 1n <> Undo.sp_w_fixes(t) : List<&2, Nat>}
          {==}
        case U.Write{}:
          %Equal.sym(List<&2, Nat>, FU.fix_codes(t), Undo.sp_w_fixes(t), una.fixes(t)) : {2n <> _ == 2n <> Undo.sp_w_fixes(t) : List<&2, Nat>}
          {==}

def una.seens(ss: List<&2, U.Seen>) -> {FU.seen_codes(ss) == Undo.sp_w_seens(ss) : List<&2, Nat>}:
  match ss:
    case Nil{}:
      {==}
    case Con{x, +t}:
      match x:
        case U.Same{}:
          %Equal.sym(List<&2, Nat>, FU.seen_codes(t), Undo.sp_w_seens(t), una.seens(t)) : {0n <> _ == 0n <> Undo.sp_w_seens(t) : List<&2, Nat>}
          {==}
        case U.Differs{}:
          %Equal.sym(List<&2, Nat>, FU.seen_codes(t), Undo.sp_w_seens(t), una.seens(t)) : {1n <> _ == 1n <> Undo.sp_w_seens(t) : List<&2, Nat>}
          {==}
        case U.Skipped{}:
          %Equal.sym(List<&2, Nat>, FU.seen_codes(t), Undo.sp_w_seens(t), una.seens(t)) : {2n <> _ == 2n <> Undo.sp_w_seens(t) : List<&2, Nat>}
          {==}

def una.code(m: Maybe<&2, Nat>) -> {FU.code_of_maybe(m) == Undo.sp_w_maybe(m) : Nat}:
  match m:
    case None{}:
      {==}
    case Some{t}:
      {==}

def una.act(a: U.Act, rest: String) -> {FU.put_act(a, rest) == Undo.sp_w_act(a, rest) : String}:
  match a:
    case U.Took{}:
      {==}
    case U.Restore{t}:
      {==}
    case U.Refused{}:
      {==}
    case U.Compare{t}:
      {==}
    case U.NoSnapshot{}:
      {==}

def una.step(r: U.St & U.Act) -> {FU.put_step(r) == Undo.sp_w_step(r) : String}:
  match r:
    case (st, a):
      match st:
        case U.St{+l, +b}:
          %Equal.sym(Nat, FU.code_of_maybe(b), Undo.sp_w_maybe(b), una.code(b)) : {FU.put_act(a, Wr.put_list(~Nat, ~Wr.put_nat, l, Wr.put_nat(_, ""))) == Undo.sp_w_act(a, LawsBase.wire_spell_nats(l, Wr.put_nat(Undo.sp_w_maybe(b), ""))) : String}
          %Wire.wire_nats_spells(l, Wr.put_nat(Undo.sp_w_maybe(b), "")) : {FU.put_act(a, Wr.put_list(~Nat, ~Wr.put_nat, l, Wr.put_nat(Undo.sp_w_maybe(b), ""))) == Undo.sp_w_act(a, _) : String}
          una.act(a, Wr.put_list(~Nat, ~Wr.put_nat, l, Wr.put_nat(Undo.sp_w_maybe(b), "")))

def una.reply(q: FU.Req) -> {FU.answer(q) == Undo.sp_w_reply(q) : String}:
  match q:
    case FU.QStep{st, e}:
      una.step(U.step(st, e))
    case FU.QFix{+rows}:
      +fs = U.fixes(rows)
      %una.fixes(fs) : {Wr.put_list(~Nat, ~Wr.put_nat, FU.fix_codes(fs), "") == LawsBase.wire_spell_nats(_, "") : String}
      Wire.wire_nats_spells(FU.fix_codes(fs), "")
    case FU.QSeen{+rows}:
      +ss = U.seens(rows)
      %una.seens(ss) : {Wr.put_list(~Nat, ~Wr.put_nat, FU.seen_codes(ss), "") == LawsBase.wire_spell_nats(_, "") : String}
      Wire.wire_nats_spells(FU.seen_codes(ss), "")

def Undo.undo_entry_answers(q, h):
  %Equal.sym(Wr.Dec<FU.Req>, FU.get_req(Undo.sp_w_req(q, "")), Wr.Got{q, ""}, LAR.unq.req(q, "", h)) : {FU.ffi.got(_) == Undo.sp_w_reply(q) : String}
  una.reply(q)
