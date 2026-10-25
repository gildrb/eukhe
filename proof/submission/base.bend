# eukhe: lemmas of the proofs of area submission

import Base
import ../../bend/submission.bend as Sb
import ../../bend/ffi_submission.bend as FSb
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../base/wire.bend as LWire
import ../base/logic/logic.bend as LLogicLogic
import ../base/nat.bend as LNat
import ../../laws/submission.bend as Submission

def sb_both(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool} & {b == True{} : Bool}:
  match a:
    case True{}:
      ({==}, e)
    case False{}:
      LLogicLogic.absurd({False{} == True{} : Bool} & {b == True{} : Bool}, e)

def sb_nat(+n: Nat, +rest: String, h: {LawsBase.wire_fits(n) == True{} : Bool}) -> {Wr.Got{n, rest} == Wr.get_nat(Wr.put_nat(n, rest)) : Wr.Dec<Nat>}:
  Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(n, rest)), Wr.Got{n, rest}, Wire.wire_nat_round_trip(n, rest, h))

def sb_dec_answered(+e: Nat, +a: Nat, +rest: String, hs: {LawsBase.wire_fits(e) == True{} : Bool} & {LawsBase.wire_fits(a) == True{} : Bool}) -> {FSb.get_sub(Wr.get_nat(Submission.spell_sub(Sb.InAnswered{e, a}, rest))) == Wr.Got{Sb.InAnswered{e, a}, rest} : Wr.Dec<Sb.Sub>}:
  (h1, h2) = hs
  %sb_nat(e, Wr.put_nat(a, rest), h1) : {FSb.get_sub.two(_) == Wr.Got{Sb.InAnswered{e, a}, rest} : Wr.Dec<Sb.Sub>}
  %sb_nat(a, rest, h2) : {FSb.get_sub.answer(e, _) == Wr.Got{Sb.InAnswered{e, a}, rest} : Wr.Dec<Sb.Sub>}
  {==}

# a spelled submission whose ids fit reads back, and the rest is untouched
def sb_dec_sub(+s: Sb.Sub, +rest: String, sf: {Submission.sub_fits(s) == True{} : Bool}) -> {FSb.get_sub(Wr.get_nat(Submission.spell_sub(s, rest))) == Wr.Got{s, rest} : Wr.Dec<Sb.Sub>}:
  match s:
    case Sb.InQueued{}:
      {==}
    case Sb.InPlaced{+e}:
      %sb_nat(e, rest, sf) : {FSb.get_sub.one(_, 0n) == Wr.Got{Sb.InPlaced{e}, rest} : Wr.Dec<Sb.Sub>}
      {==}
    case Sb.InAnswered{+e, +a}:
      sb_dec_answered(e, a, rest, sb_both(LawsBase.wire_fits(e), LawsBase.wire_fits(a), sf))
    case Sb.InDropped{m}:
      match m:
        case None{}:
          {==}
        case Some{+e}:
          %sb_nat(e, rest, sf) : {FSb.get_sub.one(_, 1n) == Wr.Got{Sb.InDropped{Some{e}}, rest} : Wr.Dec<Sb.Sub>}
          {==}
    case Sb.WrQueued{}:
      {==}
    case Sb.WrPlaced{+e}:
      %sb_nat(e, rest, sf) : {FSb.get_sub.one(_, 2n) == Wr.Got{Sb.WrPlaced{e}, rest} : Wr.Dec<Sb.Sub>}
      {==}
    case Sb.WrDropped{}:
      {==}

# a spelled change whose id fits reads back, and the rest is untouched
def sb_dec_change(+c: Sb.Change, +rest: String, cf: {Submission.change_fits(c) == True{} : Bool}) -> {FSb.get_change(Wr.get_nat(Submission.spell_change(c, rest))) == Wr.Got{c, rest} : Wr.Dec<Sb.Change>}:
  match c:
    case Sb.Place{+e}:
      %sb_nat(e, rest, cf) : {FSb.get_change.one(_, 0n) == Wr.Got{Sb.Place{e}, rest} : Wr.Dec<Sb.Change>}
      {==}
    case Sb.Answer{+a}:
      %sb_nat(a, rest, cf) : {FSb.get_change.one(_, 1n) == Wr.Got{Sb.Answer{a}, rest} : Wr.Dec<Sb.Change>}
      {==}
    case Sb.Drop{}:
      {==}

def sb_put_sub(x: Sb.Sub, rest: String) -> {FSb.put_sub(x, rest) == Submission.spell_sub(x, rest) : String}:
  match x:
    case Sb.InQueued{}:
      {==}
    case Sb.InPlaced{e}:
      {==}
    case Sb.InAnswered{e, a}:
      {==}
    case Sb.InDropped{m}:
      match m:
        case None{}:
          {==}
        case Some{e}:
          {==}
    case Sb.WrQueued{}:
      {==}
    case Sb.WrPlaced{e}:
      {==}
    case Sb.WrDropped{}:
      {==}

def sb_put_out(o: Sb.Out) -> {FSb.put_out(o) == Submission.spell_out(o) : String}:
  match o:
    case Sb.Stays{}:
      {==}
    case Sb.Moves{x}:
      %sb_put_sub(x, "") : {FSb.put_out(Sb.Moves{x}) == Wr.put_nat(1n, _) : String}
      {==}
    case Sb.Refused{y}:
      match y:
        case Sb.NotQueued{}:
          {==}
        case Sb.NotPlacedInput{}:
          {==}

# the request reads back: the entry is at its last step
def sb_reads(+s: Sb.Sub, +c: Sb.Change, +rest: String, sf: {Submission.sub_fits(s) == True{} : Bool}, cf: {Submission.change_fits(c) == True{} : Bool}) -> {FSb.ffi(Submission.spell_req(s, c, rest)) == FSb.ffi.done(s, c, Wr.end(rest)) : String}:
  %Equal.sym(Wr.Dec<Sb.Sub>, FSb.get_sub(Wr.get_nat(Submission.spell_sub(s, Submission.spell_change(c, rest)))), Wr.Got{s, Submission.spell_change(c, rest)}, sb_dec_sub(s, Submission.spell_change(c, rest), sf)) : {FSb.ffi.got(_) == FSb.ffi.done(s, c, Wr.end(rest)) : String}
  %Equal.sym(Wr.Dec<Sb.Change>, FSb.get_change(Wr.get_nat(Submission.spell_change(c, rest))), Wr.Got{c, rest}, sb_dec_change(c, rest, cf)) : {FSb.ffi.change(s, _) == FSb.ffi.done(s, c, Wr.end(rest)) : String}
  {==}

# the tail of an input: x2 is the tag t then x3, and x3 is y
def sb_sub(-t: Nat, -x2: String, -x3: String, -y: String, e1: {x3 == y : String}, es: {x2 == Wr.put_nat(t, x3) : String}) -> {x2 == Wr.put_nat(t, y) : String}:
  %e1 : {x2 == Wr.put_nat(t, _) : String}
  es

def sb_ch_place(+x2: String, +x3: String, -s: Sb.Sub, es: {x2 == Wr.put_nat(0n, x3) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x3) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSb.ffi.change(s, FSb.get_change.one(d, 0n))) == False{} : Bool}) -> Sigma<&1, &1, Sb.Change, c => {x2 == Submission.spell_change(c, "") : String}>:
  match d:
    case Wr.Got{+e, r}:
      match r:
        case SNil{}:
          (Sb.Place{e}, sb_sub(0n, x2, x3, Wr.put_nat(e, ""), Wire.wire_nat_exact(x3, e, "", ed), es))
        case SCon{h, t}:
          LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Change, c => {x2 == Submission.spell_change(c, "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Change, c => {x2 == Submission.spell_change(c, "") : String}>, ok)

def sb_ch_answer(+x2: String, +x3: String, -s: Sb.Sub, es: {x2 == Wr.put_nat(1n, x3) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x3) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSb.ffi.change(s, FSb.get_change.one(d, 1n))) == False{} : Bool}) -> Sigma<&1, &1, Sb.Change, c => {x2 == Submission.spell_change(c, "") : String}>:
  match d:
    case Wr.Got{+a, r}:
      match r:
        case SNil{}:
          (Sb.Answer{a}, sb_sub(1n, x2, x3, Wr.put_nat(a, ""), Wire.wire_nat_exact(x3, a, "", ed), es))
        case SCon{h, t}:
          LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Change, c => {x2 == Submission.spell_change(c, "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Change, c => {x2 == Submission.spell_change(c, "") : String}>, ok)

# a change read whole with nothing left is a spelled change
def sb_ch(+x2: String, -s: Sb.Sub, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x2) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSb.ffi.change(s, FSb.get_change(d))) == False{} : Bool}) -> Sigma<&1, &1, Sb.Change, c => {x2 == Submission.spell_change(c, "") : String}>:
  match d:
    case Wr.Got{+t, +x3}:
      match t:
        case 0n:
          sb_ch_place(x2, x3, s, Wire.wire_nat_exact(x2, 0n, x3, ed), Wr.get_nat(x3), {==}, ok)
        case 1n:
          sb_ch_answer(x2, x3, s, Wire.wire_nat_exact(x2, 1n, x3, ed), Wr.get_nat(x3), {==}, ok)
        case 2n:
          match x3:
            case SNil{}:
              (Sb.Drop{}, Wire.wire_nat_exact(x2, 2n, "", ed))
            case SCon{h, r}:
              LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Change, c => {x2 == Submission.spell_change(c, "") : String}>, ok)
        case 3n+u:
          LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Change, c => {x2 == Submission.spell_change(c, "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Change, c => {x2 == Submission.spell_change(c, "") : String}>, ok)

def sb_join.eq(-x: String, -x2: String, -s: Sb.Sub, -c: Sb.Change, e: {x2 == Submission.spell_change(c, "") : String}, es: {x == Submission.spell_sub(s, x2) : String}) -> {x == Submission.spell_sub(s, Submission.spell_change(c, "")) : String}:
  %e : {x == Submission.spell_sub(s, _) : String}
  es

# x is a spelled submission, then x2, a spelled change
def sb_join(-x: String, -x2: String, +s: Sb.Sub, es: {x == Submission.spell_sub(s, x2) : String}, w: Sigma<&1, &1, Sb.Change, c => {x2 == Submission.spell_change(c, "") : String}>) -> Sigma<&1, &1, Sb.Sub & Sb.Change, q => {x == Submission.spell_req(Submission.fst(q), Submission.snd(q), "") : String}>:
  (c, e) = w
  ((s, c), sb_join.eq(x, x2, s, c, e, es))

def sb_ex_placed(+x: String, +x1: String, es: {x == Wr.put_nat(1n, x1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x1) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSb.ffi.got(FSb.get_sub.one(d, 0n))) == False{} : Bool}) -> Sigma<&1, &1, Sb.Sub & Sb.Change, q => {x == Submission.spell_req(Submission.fst(q), Submission.snd(q), "") : String}>:
  match d:
    case Wr.Got{+e, +x2}:
      sb_join(x, x2, Sb.InPlaced{e}, sb_sub(1n, x, x1, Wr.put_nat(e, x2), Wire.wire_nat_exact(x1, e, x2, ed), es), sb_ch(x2, Sb.InPlaced{e}, Wr.get_nat(x2), {==}, ok))
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Sub & Sb.Change, q => {x == Submission.spell_req(Submission.fst(q), Submission.snd(q), "") : String}>, ok)

def sb_ex_dropped_at(+x: String, +x1: String, es: {x == Wr.put_nat(4n, x1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x1) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSb.ffi.got(FSb.get_sub.one(d, 1n))) == False{} : Bool}) -> Sigma<&1, &1, Sb.Sub & Sb.Change, q => {x == Submission.spell_req(Submission.fst(q), Submission.snd(q), "") : String}>:
  match d:
    case Wr.Got{+e, +x2}:
      sb_join(x, x2, Sb.InDropped{Some{e}}, sb_sub(4n, x, x1, Wr.put_nat(e, x2), Wire.wire_nat_exact(x1, e, x2, ed), es), sb_ch(x2, Sb.InDropped{Some{e}}, Wr.get_nat(x2), {==}, ok))
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Sub & Sb.Change, q => {x == Submission.spell_req(Submission.fst(q), Submission.snd(q), "") : String}>, ok)

def sb_ex_written(+x: String, +x1: String, es: {x == Wr.put_nat(6n, x1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x1) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSb.ffi.got(FSb.get_sub.one(d, 2n))) == False{} : Bool}) -> Sigma<&1, &1, Sb.Sub & Sb.Change, q => {x == Submission.spell_req(Submission.fst(q), Submission.snd(q), "") : String}>:
  match d:
    case Wr.Got{+e, +x2}:
      sb_join(x, x2, Sb.WrPlaced{e}, sb_sub(6n, x, x1, Wr.put_nat(e, x2), Wire.wire_nat_exact(x1, e, x2, ed), es), sb_ch(x2, Sb.WrPlaced{e}, Wr.get_nat(x2), {==}, ok))
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Sub & Sb.Change, q => {x == Submission.spell_req(Submission.fst(q), Submission.snd(q), "") : String}>, ok)

def sb_ex_answer(+x: String, -x1: String, +e: Nat, +x2: String, es: {x == Wr.put_nat(2n, Wr.put_nat(e, x2)) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x2) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSb.ffi.got(FSb.get_sub.answer(e, d))) == False{} : Bool}) -> Sigma<&1, &1, Sb.Sub & Sb.Change, q => {x == Submission.spell_req(Submission.fst(q), Submission.snd(q), "") : String}>:
  match d:
    case Wr.Got{+a, +x3}:
      sb_join(x, x3, Sb.InAnswered{e, a}, sb_sub(2n, x, Wr.put_nat(e, x2), Wr.put_nat(e, Wr.put_nat(a, x3)), Equal.cong(String, String, z => Wr.put_nat(e, z), x2, Wr.put_nat(a, x3), Wire.wire_nat_exact(x2, a, x3, ed)), es), sb_ch(x3, Sb.InAnswered{e, a}, Wr.get_nat(x3), {==}, ok))
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Sub & Sb.Change, q => {x == Submission.spell_req(Submission.fst(q), Submission.snd(q), "") : String}>, ok)

def sb_ex_answered(+x: String, +x1: String, es: {x == Wr.put_nat(2n, x1) : String}, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x1) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSb.ffi.got(FSb.get_sub.two(d))) == False{} : Bool}) -> Sigma<&1, &1, Sb.Sub & Sb.Change, q => {x == Submission.spell_req(Submission.fst(q), Submission.snd(q), "") : String}>:
  match d:
    case Wr.Got{+e, +x2}:
      sb_ex_answer(x, x1, e, x2, sb_sub(2n, x, x1, Wr.put_nat(e, x2), Wire.wire_nat_exact(x1, e, x2, ed), es), Wr.get_nat(x2), {==}, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Sub & Sb.Change, q => {x == Submission.spell_req(Submission.fst(q), Submission.snd(q), "") : String}>, ok)

# a reply that is no error comes from a spelled request
def sb_ex(+x: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(x) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSb.ffi.got(FSb.get_sub(d))) == False{} : Bool}) -> Sigma<&1, &1, Sb.Sub & Sb.Change, q => {x == Submission.spell_req(Submission.fst(q), Submission.snd(q), "") : String}>:
  match d:
    case Wr.Got{+t, +x1}:
      match t:
        case 0n:
          sb_join(x, x1, Sb.InQueued{}, Wire.wire_nat_exact(x, 0n, x1, ed), sb_ch(x1, Sb.InQueued{}, Wr.get_nat(x1), {==}, ok))
        case 1n:
          sb_ex_placed(x, x1, Wire.wire_nat_exact(x, 1n, x1, ed), Wr.get_nat(x1), {==}, ok)
        case 2n:
          sb_ex_answered(x, x1, Wire.wire_nat_exact(x, 2n, x1, ed), Wr.get_nat(x1), {==}, ok)
        case 3n:
          sb_join(x, x1, Sb.InDropped{None{}}, Wire.wire_nat_exact(x, 3n, x1, ed), sb_ch(x1, Sb.InDropped{None{}}, Wr.get_nat(x1), {==}, ok))
        case 4n:
          sb_ex_dropped_at(x, x1, Wire.wire_nat_exact(x, 4n, x1, ed), Wr.get_nat(x1), {==}, ok)
        case 5n:
          sb_join(x, x1, Sb.WrQueued{}, Wire.wire_nat_exact(x, 5n, x1, ed), sb_ch(x1, Sb.WrQueued{}, Wr.get_nat(x1), {==}, ok))
        case 6n:
          sb_ex_written(x, x1, Wire.wire_nat_exact(x, 6n, x1, ed), Wr.get_nat(x1), {==}, ok)
        case 7n:
          sb_join(x, x1, Sb.WrDropped{}, Wire.wire_nat_exact(x, 7n, x1, ed), sb_ch(x1, Sb.WrDropped{}, Wr.get_nat(x1), {==}, ok))
        case 8n+u:
          LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Sub & Sb.Change, q => {x == Submission.spell_req(Submission.fst(q), Submission.snd(q), "") : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.pt.absurd(Sigma<&1, &1, Sb.Sub & Sb.Change, q => {x == Submission.spell_req(Submission.fst(q), Submission.snd(q), "") : String}>, ok)
