# eukhe: the proof of LAW tiny_ffi_exact
# The entry reads every input as the spec's reader does and answers the
# spec's pick (the model's first available model of the chain).

import Base
import ../../bend/ffi_tiny.bend as FTn
import ../../bend/tiny.bend as Tn
import ../../bend/wire.bend as Wr
import ../../laws/tiny/pick.bend as Tiny

def tx.elem(xs: List<&2, Nat>, +x: Nat) -> {Tn.elem(xs, x) == Tiny.sp_in(xs, x) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case y <> +rest:
      %Equal.sym(Bool, Tn.elem(rest, x), Tiny.sp_in(rest, x), tx.elem(rest, x)) : {Bool.or(Nat.is_eq(y, x), _) == Bool.or(Nat.is_eq(y, x), Tiny.sp_in(rest, x)) : Bool}
      {==}

def tx.at(hit: Bool, -m: Nat, -rest: List<&2, Nat>, -up: List<&2, Nat>, ih: {Tn.pick(rest, up) == Tiny.sp_pick(rest, up) : Tn.Pick}) -> {Tn.pick.go(m <> rest, up, hit) == Tiny.sp_pick.at(hit, m, Tiny.sp_pick(rest, up)) : Tn.Pick}:
  match hit:
    case True{}:
      {==}
    case False{}:
      ih

def tx.pick(chain: List<&2, Nat>, +up: List<&2, Nat>) -> {Tn.pick(chain, up) == Tiny.sp_pick(chain, up) : Tn.Pick}:
  match chain:
    case Nil{}:
      {==}
    case +m <> +rest:
      %Equal.sym(Bool, Tn.elem(up, m), Tiny.sp_in(up, m), tx.elem(up, m)) : {Tn.pick.go(m <> rest, up, _) == Tiny.sp_pick(m <> rest, up) : Tn.Pick}
      tx.at(Tiny.sp_in(up, m), m, rest, up, tx.pick(rest, up))

def tx.spell(p: Tn.Pick) -> {FTn.put_pick(p, SNil{}) == Tiny.sp_spell_pick(p) : String}:
  match p:
    case Tn.Use{m}:
      {==}
    case Tn.Unavailable{}:
      {==}

def tx.up(c: List<&2, Nat>, r: Wr.Dec<List<&2, Nat>>) -> {FTn.get_req.up(c, r) == Tiny.sp_read.up(c, r) : Wr.Dec<FTn.Req>}:
  match r:
    case Wr.Got{u, s}:
      {==}
    case Wr.Bad{}:
      {==}

def tx.chain(r: Wr.Dec<List<&2, Nat>>) -> {FTn.get_req.chain(r) == Tiny.sp_read.chain(r) : Wr.Dec<FTn.Req>}:
  match r:
    case Wr.Got{c, s}:
      tx.up(c, Wr.get_list(~Nat, ~Wr.get_nat, s))
    case Wr.Bad{}:
      {==}

def tx.end(b: Bool, q: FTn.Req) -> {FTn.reply(b, q) == Tiny.sp_pick_end(b, q) : String}:
  match b:
    case True{}:
      match q:
        case FTn.Req{+c, +u}:
          %Equal.sym(Tn.Pick, Tn.pick(c, u), Tiny.sp_pick(c, u), tx.pick(c, u)) : {FTn.put_pick(_, SNil{}) == Tiny.sp_pick_end(True{}, FTn.Req{c, u}) : String}
          tx.spell(Tiny.sp_pick(c, u))
    case False{}:
      {==}

def tx.run(r: Wr.Dec<FTn.Req>) -> {FTn.answer(r) == Tiny.sp_pick_run(r) : String}:
  match r:
    case Wr.Got{q, s}:
      tx.end(Wr.end(s), q)
    case Wr.Bad{}:
      {==}

def Tiny.tiny_ffi_exact(s):
  %Equal.sym(Wr.Dec<FTn.Req>, FTn.get_req.chain(Wr.get_list(~Nat, ~Wr.get_nat, s)), Tiny.sp_read.chain(Wr.get_list(~Nat, ~Wr.get_nat, s)), tx.chain(Wr.get_list(~Nat, ~Wr.get_nat, s))) : {FTn.answer(_) == Tiny.sp_pick_entry(s) : String}
  tx.run(Tiny.sp_read(s))
