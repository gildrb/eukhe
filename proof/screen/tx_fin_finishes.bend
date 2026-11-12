# eukhe: the proof of LAW tx_fin_finishes
#
# PROOF: block by block along the edit (induction on the blocks): a block of
# id x becomes fin1 of it, which tx_finished.at accepts for each state; a
# block of another id is kept.

import Base
import ../../bend/screen.bend as Sc
import ../../laws/screen/events.bend as ScreenEvents
import ./base/events.bend as LAScreenEvents

def fin.hit(+i: Nat, +s: Sc.St, +l: Nat, +x: Nat, e: {Nat.is_eq(i, x) == True{} : Bool}) -> {ScreenEvents.tx_finished.blk(x, Sc.Blk{i, s, l}, Sc.edit.one(Sc.Blk{i, s, l}, None{})) == True{} : Bool}:
  match s:
    case Sc.Active{}:
      %Equal.sym(Bool, Nat.is_eq(i, x), True{}, e) : {ScreenEvents.tx_finished.at(_, i, Sc.Active{}, l, i, Sc.Final{}, l) == True{} : Bool}
      LAScreenEvents.ev.and3(Nat.is_eq(i, i), Nat.is_eq(l, l), True{}, LAScreenEvents.ev.t(i), LAScreenEvents.ev.t(l), {==})
    case Sc.Final{}:
      %Equal.sym(Bool, Nat.is_eq(i, x), True{}, e) : {ScreenEvents.tx_finished.at(_, i, Sc.Final{}, l, i, Sc.Final{}, l) == True{} : Bool}
      LAScreenEvents.ev.and3(Nat.is_eq(i, i), Nat.is_eq(l, l), True{}, LAScreenEvents.ev.t(i), LAScreenEvents.ev.t(l), {==})
    case Sc.Comm{}:
      %Equal.sym(Bool, Nat.is_eq(i, x), True{}, e) : {ScreenEvents.tx_finished.at(_, i, Sc.Comm{}, l, i, Sc.Comm{}, l) == True{} : Bool}
      LAScreenEvents.ev.and3(Nat.is_eq(i, i), Nat.is_eq(l, l), True{}, LAScreenEvents.ev.t(i), LAScreenEvents.ev.t(l), {==})

def fin.miss(+i: Nat, +s: Sc.St, +l: Nat, +x: Nat, e: {Nat.is_eq(i, x) == False{} : Bool}) -> {ScreenEvents.tx_finished.blk(x, Sc.Blk{i, s, l}, Sc.Blk{i, s, l}) == True{} : Bool}:
  match s:
    case Sc.Active{}:
      %Equal.sym(Bool, Nat.is_eq(i, x), False{}, e) : {ScreenEvents.tx_finished.at(_, i, Sc.Active{}, l, i, Sc.Active{}, l) == True{} : Bool}
      LAScreenEvents.ev.and3(Nat.is_eq(i, i), Nat.is_eq(l, l), True{}, LAScreenEvents.ev.t(i), LAScreenEvents.ev.t(l), {==})
    case Sc.Final{}:
      %Equal.sym(Bool, Nat.is_eq(i, x), False{}, e) : {ScreenEvents.tx_finished.at(_, i, Sc.Final{}, l, i, Sc.Final{}, l) == True{} : Bool}
      LAScreenEvents.ev.and3(Nat.is_eq(i, i), Nat.is_eq(l, l), True{}, LAScreenEvents.ev.t(i), LAScreenEvents.ev.t(l), {==})
    case Sc.Comm{}:
      %Equal.sym(Bool, Nat.is_eq(i, x), False{}, e) : {ScreenEvents.tx_finished.at(_, i, Sc.Comm{}, l, i, Sc.Comm{}, l) == True{} : Bool}
      LAScreenEvents.ev.and3(Nat.is_eq(i, i), Nat.is_eq(l, l), True{}, LAScreenEvents.ev.t(i), LAScreenEvents.ev.t(l), {==})

def fin.at(+i: Nat, +s: Sc.St, +l: Nat, +br: List<&2, Sc.Blk>, +x: Nat, hit: Bool, e: {Nat.is_eq(i, x) == hit : Bool}, ih: {ScreenEvents.tx_finished(x, br, Sc.edit.go(br, x, None{}, Sc.bid.at(br, x))) == True{} : Bool}) -> {ScreenEvents.tx_finished(x, Sc.Blk{i, s, l} <> br, Sc.edit.go(Sc.Blk{i, s, l} <> br, x, None{}, hit)) == True{} : Bool}:
  match hit:
    case True{}:
      LAScreenEvents.ev.and_t(ScreenEvents.tx_finished.blk(x, Sc.Blk{i, s, l}, Sc.edit.one(Sc.Blk{i, s, l}, None{})), ScreenEvents.tx_finished(x, br, Sc.edit.go(br, x, None{}, Sc.bid.at(br, x))), fin.hit(i, s, l, x, e), ih)
    case False{}:
      LAScreenEvents.ev.and_t(ScreenEvents.tx_finished.blk(x, Sc.Blk{i, s, l}, Sc.Blk{i, s, l}), ScreenEvents.tx_finished(x, br, Sc.edit.go(br, x, None{}, Sc.bid.at(br, x))), fin.miss(i, s, l, x, e), ih)

def fin.blocks(bs: List<&2, Sc.Blk>, +x: Nat) -> {ScreenEvents.tx_finished(x, bs, Sc.edit.go(bs, x, None{}, Sc.bid.at(bs, x))) == True{} : Bool}:
  match bs:
    case Nil{}:
      {==}
    case b <> +br:
      match b:
        case Sc.Blk{+i, s, l}:
          fin.at(i, s, l, br, x, Nat.is_eq(i, x), {==}, fin.blocks(br, x))

def fin.law(+t: Sc.Tx, +x: Nat) -> {ScreenEvents.tx_finished(x, Sc.Tx.blocks(t), Sc.Tx.blocks(Sc.step(t, Sc.Fin{x}))) == True{} : Bool}:
  match t:
    case Sc.Tx{bs, n, w}:
      fin.blocks(bs, x)

def ScreenEvents.tx_fin_finishes(t, x):
  fin.law(t, x)
