# eukhe: the proof of LAW wire_nat_overlong

import Base
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic

# no Nat is below 0
def wo_lt0(p: Nat, -G: Type, h: {Nat.is_lt(p, 0n) == True{} : Bool}) -> G:
  match p:
    case 0n:
      LLogicLogic.wn_absurd(G, h)
    case 1n+q:
      LLogicLogic.wn_absurd(G, h)

# the char of a digit below 10 is the token of that digit
def wo_tok(+d: Nat, h: {Nat.is_lt(d, 10n) == True{} : Bool}) -> {Wr.tok(LawsBase.wire_dec_char(d)) == Wr.Dig{d} : Wr.Tok}:
  match d:
    case 0n:
      {==}
    case 1n:
      {==}
    case 2n:
      {==}
    case 3n:
      {==}
    case 4n:
      {==}
    case 5n:
      {==}
    case 6n:
      {==}
    case 7n:
      {==}
    case 8n:
      {==}
    case 9n:
      {==}
    case 10n+p:
      wo_lt0(p, {Wr.tok(LawsBase.wire_dec_char(10n+p)) == Wr.Dig{10n+p} : Wr.Tok}, h)

# with a digit token in hand and at least k more digit chars after it, the
# digit loop with k digits left refuses: a digit follows the last one it may read
def wo_go(k: Nat, +ds: List<&2, Nat>, +rest: String, +d: Nat, +v: Nat,
  +hd: {LawsBase.wire_digits_all(ds) == True{} : Bool},
  hl: {Nat.is_lt(k, 1n+List.length(&2, Nat, ds)) == True{} : Bool}) ->
  {Wr.get_nat.go(k, Wr.Dig{d}, LawsBase.wire_digit_chars(ds, rest), v) == Wr.Bad{} : Wr.Dec<Nat>}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      match ds:
        case Nil{}:
          wo_lt0(j, {Wr.get_nat.go(1n+j, Wr.Dig{d}, LawsBase.wire_digit_chars([], rest), v) == Wr.Bad{} : Wr.Dec<Nat>}, hl)
        case Con{+d2, +t}:
          +h2 = LLogicBool.wn_and_l(Nat.is_lt(d2, 10n), LawsBase.wire_digits_all(t), hd)
          +ht = LLogicBool.wn_and_r(Nat.is_lt(d2, 10n), LawsBase.wire_digits_all(t), hd)
          %Equal.sym(Wr.Tok, Wr.tok(LawsBase.wire_dec_char(d2)), Wr.Dig{d2}, wo_tok(d2, h2)) : {Wr.get_nat.go(j, _, LawsBase.wire_digit_chars(t, rest), Nat.add(d, Nat.mul(10n, v))) == Wr.Bad{} : Wr.Dec<Nat>}
          wo_go(j, t, rest, d2, Nat.add(d, Nat.mul(10n, v)), ht, hl)

# the first digit d1 and the token of the second in hand: 0 stands alone
# (a digit follows it), any other starts the loop with 13 digits left
def wo_lead(d1: Nat, +t: List<&2, Nat>, +rest: String, +d2: Nat,
  ht: {LawsBase.wire_digits_all(t) == True{} : Bool},
  hl: {Nat.is_lt(13n, 1n+List.length(&2, Nat, t)) == True{} : Bool}) ->
  {Wr.get_nat.lead(d1, Wr.Dig{d2}, LawsBase.wire_digit_chars(t, rest)) == Wr.Bad{} : Wr.Dec<Nat>}:
  match d1:
    case 0n:
      {==}
    case 1n+p:
      wo_go(13n, t, rest, d2, 1n+p, ht, hl)

# the first two digits read, the rest as the loop above
def wo_top(+ds: List<&2, Nat>, +rest: String, +h: {LawsBase.wire_overlong(ds) == True{} : Bool}) ->
  {Wr.get_nat(LawsBase.wire_digit_chars(ds, rest)) == Wr.Bad{} : Wr.Dec<Nat>}:
  match ds:
    case Nil{}:
      LLogicLogic.wn_absurd({Wr.get_nat(LawsBase.wire_digit_chars([], rest)) == Wr.Bad{} : Wr.Dec<Nat>}, h)
    case Con{+d1, +u}:
      match u:
        case Nil{}:
          LLogicLogic.wn_absurd({Wr.get_nat(LawsBase.wire_digit_chars([d1], rest)) == Wr.Bad{} : Wr.Dec<Nat>},
            LLogicBool.wn_and_r(LawsBase.wire_digits_all([d1]), Nat.is_lt(14n, 1n), h))
        case Con{+d2, +t}:
          +hd = LLogicBool.wn_and_l(LawsBase.wire_digits_all(d1 <> d2 <> t), Nat.is_lt(14n, 2n+List.length(&2, Nat, t)), h)
          +hl = LLogicBool.wn_and_r(LawsBase.wire_digits_all(d1 <> d2 <> t), Nat.is_lt(14n, 2n+List.length(&2, Nat, t)), h)
          +h1 = LLogicBool.wn_and_l(Nat.is_lt(d1, 10n), LawsBase.wire_digits_all(d2 <> t), hd)
          +hu = LLogicBool.wn_and_r(Nat.is_lt(d1, 10n), LawsBase.wire_digits_all(d2 <> t), hd)
          +h2 = LLogicBool.wn_and_l(Nat.is_lt(d2, 10n), LawsBase.wire_digits_all(t), hu)
          +ht = LLogicBool.wn_and_r(Nat.is_lt(d2, 10n), LawsBase.wire_digits_all(t), hu)
          %Equal.sym(Wr.Tok, Wr.tok(LawsBase.wire_dec_char(d1)), Wr.Dig{d1}, wo_tok(d1, h1)) : {Wr.get_nat.first(_, SCon{LawsBase.wire_dec_char(d2), LawsBase.wire_digit_chars(t, rest)}) == Wr.Bad{} : Wr.Dec<Nat>}
          %Equal.sym(Wr.Tok, Wr.tok(LawsBase.wire_dec_char(d2)), Wr.Dig{d2}, wo_tok(d2, h2)) : {Wr.get_nat.lead(d1, _, LawsBase.wire_digit_chars(t, rest)) == Wr.Bad{} : Wr.Dec<Nat>}
          wo_lead(d1, t, rest, d2, ht, hl)

def Wire.wire_nat_overlong(ds, rest, h):
  wo_top(ds, rest, h)
