# eukhe: the proof of LAW replacement_terminates_any
#
# PROOF of LAW replacement_terminates_any: the laws' own build equality
# implies the model's (rtb.build: equal ids and item-wise equal numbers
# are build_eq), so every start's build in bs by rp_all_built is in bs by
# Rp.covers (rtb.covers), and replacement_terminates gives the bound.

import Base
import ../../bend/replace.bend as Rp
import ../../laws/replace.bend as Replace
import ../base/logic/bool.bend as LLogicBool
import ../wire/base/spell.bend as LAWireSpell
import ./replacement_terminates.bend as PReplacementTerminates

def rtb.nats(xs: List<&2, Nat>, ys: List<&2, Nat>, +e: {Replace.rp_nats_same(xs, ys) == True{} : Bool}) -> {Rp.ranks_eq(xs, ys) == True{} : Bool}:
  match xs ys:
    case Nil{} Nil{}:
      {==}
    case Nil{} y <> yr:
      e
    case x <> xr Nil{}:
      e
    case +x <> +xr +y <> +yr:
      LAWireSpell.ws_and_tt(Nat.is_eq(x, y), Rp.ranks_eq(xr, yr), LLogicBool.wr_and_l(Nat.is_eq(x, y), Replace.rp_nats_same(xr, yr), e), rtb.nats(xr, yr, LLogicBool.wr_and_r(Nat.is_eq(x, y), Replace.rp_nats_same(xr, yr), e)))

def rtb.build(a: Rp.Build, b: Rp.Build, +e: {Replace.rp_build_same(a, b) == True{} : Bool}) -> {Rp.build_eq(a, b) == True{} : Bool}:
  match a b:
    case Rp.Build{+ra, +ia} Rp.Build{+rb, +ib}:
      LAWireSpell.ws_and_tt(String.eq(ia, ib), Rp.ranks_eq(ra, rb), LLogicBool.wr_and_l(String.eq(ia, ib), Replace.rp_nats_same(ra, rb), e), rtb.nats(ra, rb, LLogicBool.wr_and_r(String.eq(ia, ib), Replace.rp_nats_same(ra, rb), e)))

def rtb.or_r(x: Bool, -y: Bool, h: {y == True{} : Bool}) -> {Bool.or(x, y) == True{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      h

def rtb.has.at(p: Bool, +e0: Rp.Build, +t: List<&2, Rp.Build>, +b: Rp.Build, ep: {Replace.rp_build_same(e0, b) == p : Bool}, m: {Bool.or(p, Replace.rp_built(t, b)) == True{} : Bool}, ih: {Replace.rp_built(t, b) == True{} : Bool} -> {Rp.has(t, b) == True{} : Bool}) -> {Bool.or(Rp.build_eq(e0, b), Rp.has(t, b)) == True{} : Bool}:
  match p:
    case True{}:
      %Equal.sym(Bool, Rp.build_eq(e0, b), True{}, rtb.build(e0, b, ep)) : {Bool.or(_, Rp.has(t, b)) == True{} : Bool}
      {==}
    case False{}:
      rtb.or_r(Rp.build_eq(e0, b), Rp.has(t, b), ih(m))

# a build in bs by the laws' equality is in bs by the model's
def rtb.has(bs: List<&2, Rp.Build>, +b: Rp.Build, m: {Replace.rp_built(bs, b) == True{} : Bool}) -> {Rp.has(bs, b) == True{} : Bool}:
  match bs:
    case Nil{}:
      m
    case +e0 <> +t:
      rtb.has.at(Replace.rp_build_same(e0, b), e0, t, b, {==}, m, i => rtb.has(t, b, i))

# every start's build in bs by the laws' equality: Rp.covers holds
def rtb.covers(+bs: List<&2, Rp.Build>, ss: List<&2, Rp.Start>, +e: {Replace.rp_all_built(bs, ss) == True{} : Bool}) -> {Rp.covers(bs, ss) == True{} : Bool}:
  match ss:
    case Nil{}:
      {==}
    case s <> +rest:
      match s:
        case Rp.Start{+c, k}:
          LAWireSpell.ws_and_tt(Rp.has(bs, c), Rp.covers(bs, rest), rtb.has(bs, c, LLogicBool.wr_and_l(Replace.rp_built(bs, c), Replace.rp_all_built(bs, rest), e)), rtb.covers(bs, rest, LLogicBool.wr_and_r(Replace.rp_built(bs, c), Replace.rp_all_built(bs, rest), e)))

def Replace.replacement_terminates_any(bs, ss, cover):
  Replace.replacement_terminates(bs, ss, rtb.covers(bs, ss, cover))
