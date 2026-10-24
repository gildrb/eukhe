# eukhe: the proof of LAW compactor_ffi_step
# Every number of the request reads back (LWire.pw6.nat). The entry then
# runs line.step's decision on the lengths: a reply of a text decides on
# its length only (whether it fits the node, whether it is shorter than
# the best reply's length), never on its characters, and a best reply or
# input text only appears in the end it names, whose tag is all Rust
# reads. So the entry's answer, encoded, is the model's.

import Base
import ../../bend/compactor.bend as C
import ../../bend/ffi_compactor.bend as FC
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/compactor.bend as Compactor
import ../base/logic/bool.bend as LLogicBool
import ../base/wire.bend as LWire
import ./line_step_exact.bend as PLineStepExact

# the best reply's length as Rust sends it
def cst.mb(b: Maybe<&2, List<&2, C.W>>, bl: Nat) -> Maybe<&2, Nat>:
  match b:
    case None{}:
      None{}
    case Some{t}:
      Some{bl}

# a reply as the entry reads it
def cst.rep(r: C.Reply) -> FC.Rep:
  match r:
    case C.Erred{}:
      FC.RErr{}
    case C.Says{ws}:
      FC.RSays{Compactor.bytes(ws)}

# A reply that fits or not, shorter or not, with p more tries: the end the
# model takes names the same tag with texts or without
def cst.says_none(fit: Bool, less: Bool, p: Nat, +m: Nat, +node: Nat, -i: List<&2, C.W>, -ws: List<&2, C.W>, +len: Nat) -> {FC.put_next(C.line.says(fit, less, p, m, node, None{}, Nil{}, Nil{}, len)) == Compactor.spell_next(Compactor.step_spec.text(fit, less, p, m, node, None{}, i, ws, len)) : String}:
  match fit less:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          {==}

def cst.says_some(fit: Bool, less: Bool, p: Nat, +m: Nat, +node: Nat, -bt: List<&2, C.W>, -i: List<&2, C.W>, -ws: List<&2, C.W>, +len: Nat) -> {FC.put_next(C.line.says(fit, less, p, m, node, Some{Nil{}}, Nil{}, Nil{}, len)) == Compactor.spell_next(Compactor.step_spec.text(fit, less, p, m, node, Some{bt}, i, ws, len)) : String}:
  match fit less:
    case True{} True{}:
      {==}
    case True{} False{}:
      {==}
    case False{} False{}:
      {==}
    case False{} True{}:
      match p:
        case 0n:
          {==}
        case 1n+q:
          {==}

# a text that is not empty: by its first character's width
def cst.text(p: Nat, +m: Nat, +node: Nat, b: Maybe<&2, List<&2, C.W>>, +bl: Nat, -i: List<&2, C.W>, w: C.W, +t: List<&2, C.W>) -> {FC.put_next(FC.reply(1n+p, m, node, cst.mb(b, bl), cst.rep(C.Says{w <> t}))) == Compactor.spell_next(Compactor.step_spec(C.Lst{1n+p, m, node, b, bl, i}, C.Says{w <> t})) : String}:
  match b:
    case None{}:
      match w:
        case C.W1{}:
          cst.says_none(Nat.is_le(Compactor.bytes(C.W1{} <> t), node), True{}, p, m, node, i, C.W1{} <> t, Compactor.bytes(C.W1{} <> t))
        case C.W2{}:
          cst.says_none(Nat.is_le(Compactor.bytes(C.W2{} <> t), node), True{}, p, m, node, i, C.W2{} <> t, Compactor.bytes(C.W2{} <> t))
        case C.W3{}:
          cst.says_none(Nat.is_le(Compactor.bytes(C.W3{} <> t), node), True{}, p, m, node, i, C.W3{} <> t, Compactor.bytes(C.W3{} <> t))
        case C.W4{}:
          cst.says_none(Nat.is_le(Compactor.bytes(C.W4{} <> t), node), True{}, p, m, node, i, C.W4{} <> t, Compactor.bytes(C.W4{} <> t))
    case Some{bt}:
      match w:
        case C.W1{}:
          cst.says_some(Nat.is_le(Compactor.bytes(C.W1{} <> t), node), Nat.is_lt(Compactor.bytes(C.W1{} <> t), bl), p, m, node, bt, i, C.W1{} <> t, Compactor.bytes(C.W1{} <> t))
        case C.W2{}:
          cst.says_some(Nat.is_le(Compactor.bytes(C.W2{} <> t), node), Nat.is_lt(Compactor.bytes(C.W2{} <> t), bl), p, m, node, bt, i, C.W2{} <> t, Compactor.bytes(C.W2{} <> t))
        case C.W3{}:
          cst.says_some(Nat.is_le(Compactor.bytes(C.W3{} <> t), node), Nat.is_lt(Compactor.bytes(C.W3{} <> t), bl), p, m, node, bt, i, C.W3{} <> t, Compactor.bytes(C.W3{} <> t))
        case C.W4{}:
          cst.says_some(Nat.is_le(Compactor.bytes(C.W4{} <> t), node), Nat.is_lt(Compactor.bytes(C.W4{} <> t), bl), p, m, node, bt, i, C.W4{} <> t, Compactor.bytes(C.W4{} <> t))

# the decision on the request's values is the model's line.step
def cst.decide(l: Nat, +m: Nat, +node: Nat, i: List<&2, C.W>, r: C.Reply, b: Maybe<&2, List<&2, C.W>>, +bl: Nat) -> {FC.put_next(FC.reply(l, m, node, cst.mb(b, bl), cst.rep(r))) == Compactor.spell_next(Compactor.step_spec(C.Lst{l, m, node, b, bl, i}, r)) : String}:
  match l:
    case 0n:
      match b:
        case None{}:
          {==}
        case Some{bt}:
          {==}
    case 1n+p:
      match r:
        case C.Erred{}:
          {==}
        case C.Says{ws}:
          match ws:
            case Nil{}:
              match b:
                case None{}:
                  {==}
                case Some{bt}:
                  {==}
            case w <> t:
              cst.text(p, m, node, b, bl, i, w, t)

# the reply reads back, then the decision
def cst.reply(+l: Nat, +m: Nat, +node: Nat, b: Maybe<&2, List<&2, C.W>>, +bl: Nat, +i: List<&2, C.W>, r: C.Reply, hr: {Compactor.reply_fits(r) == True{} : Bool}) -> {FC.run(FC.get_step.tag(l, m, node, cst.mb(b, bl), Wr.get_nat(Compactor.spell_reply(r)))) == Compactor.spell_next(Compactor.step_spec(C.Lst{l, m, node, b, bl, i}, r)) : String}:
  match r:
    case C.Erred{}:
      cst.decide(l, m, node, i, C.Erred{}, b, bl)
    case C.Says{+ws}:
      %LWire.pw6.nat(Compactor.bytes(ws), "", hr) : {FC.run(FC.get_step.says(l, m, node, cst.mb(b, bl), _)) == Compactor.spell_next(Compactor.step_spec(C.Lst{l, m, node, b, bl, i}, C.Says{ws})) : String}
      cst.decide(l, m, node, i, C.Says{ws}, b, bl)

# the best reply's length reads back, then the reply
def cst.best(+l: Nat, +m: Nat, +node: Nat, b: Maybe<&2, List<&2, C.W>>, +bl: Nat, +i: List<&2, C.W>, +r: C.Reply, hb: {Compactor.best_fits(b, bl) == True{} : Bool}, hr: {Compactor.reply_fits(r) == True{} : Bool}) -> {FC.run(FC.get_step.kind(l, m, node, FC.get_mnat(Wr.get_nat(Compactor.spell_best(b, bl, Compactor.spell_reply(r)))))) == Compactor.spell_next(Compactor.step_spec(C.Lst{l, m, node, b, bl, i}, r)) : String}:
  match b:
    case None{}:
      cst.reply(l, m, node, None{}, bl, i, r, hr)
    case Some{bt}:
      %LWire.pw6.nat(bl, Compactor.spell_reply(r), hb) : {FC.run(FC.get_step.kind(l, m, node, FC.get_mnat.some(_))) == Compactor.spell_next(Compactor.step_spec(C.Lst{l, m, node, Some{bt}, bl, i}, r)) : String}
      cst.reply(l, m, node, Some{bt}, bl, i, r, hr)

def cst.fill(st: C.Lst, +r: C.Reply, +fits: {Compactor.step_fits(st, r) == True{} : Bool}) -> {FC.ffi(Compactor.spell_step(st, r)) == Compactor.spell_next(Compactor.step_spec(st, r)) : String}:
  match st:
    case C.Lst{+l, +m, +n, +b, +bl, +i}:
      +rest = Compactor.spell_best(b, bl, Compactor.spell_reply(r))
      +hl = LLogicBool.wr_and_l(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(m), Bool.and(LawsBase.wire_fits(n), Bool.and(Compactor.best_fits(b, bl), Compactor.reply_fits(r)))), fits)
      +h1 = LLogicBool.wr_and_r(LawsBase.wire_fits(l), Bool.and(LawsBase.wire_fits(m), Bool.and(LawsBase.wire_fits(n), Bool.and(Compactor.best_fits(b, bl), Compactor.reply_fits(r)))), fits)
      +hm = LLogicBool.wr_and_l(LawsBase.wire_fits(m), Bool.and(LawsBase.wire_fits(n), Bool.and(Compactor.best_fits(b, bl), Compactor.reply_fits(r))), h1)
      +h2 = LLogicBool.wr_and_r(LawsBase.wire_fits(m), Bool.and(LawsBase.wire_fits(n), Bool.and(Compactor.best_fits(b, bl), Compactor.reply_fits(r))), h1)
      +hn = LLogicBool.wr_and_l(LawsBase.wire_fits(n), Bool.and(Compactor.best_fits(b, bl), Compactor.reply_fits(r)), h2)
      +h3 = LLogicBool.wr_and_r(LawsBase.wire_fits(n), Bool.and(Compactor.best_fits(b, bl), Compactor.reply_fits(r)), h2)
      +hb = LLogicBool.wr_and_l(Compactor.best_fits(b, bl), Compactor.reply_fits(r), h3)
      +hr = LLogicBool.wr_and_r(Compactor.best_fits(b, bl), Compactor.reply_fits(r), h3)
      %LWire.pw6.nat(l, Wr.put_nat(m, Wr.put_nat(n, rest)), hl) : {FC.run(FC.get_step(_)) == Compactor.spell_next(Compactor.step_spec(C.Lst{l, m, n, b, bl, i}, r)) : String}
      %LWire.pw6.nat(m, Wr.put_nat(n, rest), hm) : {FC.run(FC.get_step.made(l, _)) == Compactor.spell_next(Compactor.step_spec(C.Lst{l, m, n, b, bl, i}, r)) : String}
      %LWire.pw6.nat(n, rest, hn) : {FC.run(FC.get_step.node(l, m, _)) == Compactor.spell_next(Compactor.step_spec(C.Lst{l, m, n, b, bl, i}, r)) : String}
      cst.best(l, m, n, b, bl, i, r, hb, hr)

def Compactor.compactor_ffi_step(st, r, fits):
  %Equal.sym(C.Next, C.line.step(st, r), Compactor.step_spec(st, r), Compactor.line_step_exact(st, r)) : {FC.ffi(Compactor.spell_step(st, r)) == Compactor.spell_next(_) : String}
  cst.fill(st, r, fits)
