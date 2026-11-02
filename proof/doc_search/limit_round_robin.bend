# eukhe: the proof of LAW limit_round_robin: the code's rounds are the spec's rounds;
# a spent budget gives zeros, so the code may stop there; a jump over d
# full rounds is d of the spec's rounds (base/rr_jump.bend), so the code may
# jump whenever rr.ok holds, and go round by round otherwise

import Base
import ../../bend/doc_search.bend as Sr
import ../../laws/doc_search.bend as DocSearch

import ./base.bend as LADocSearch
import ./base/rr_jump.bend as LARrJump

def rr.bit_eq(x: Bool, b: Nat) -> {Sr.rr.bit(x, b) == DocSearch.ds_bit(Bool.and(Nat.is_lt(0n, b), x)) : Nat}:
  match x b:
    case True{} 0n:
      {==}
    case True{} 1n+c:
      {==}
    case False{} 0n:
      {==}
    case False{} 1n+c:
      {==}

def rr.give_eq(cs: List<&2, Nat>, +r: Nat, +b: Nat) -> {Sr.rr.give(cs, r, b) == DocSearch.ds_round(cs, r, b) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> t:
      +x = Nat.is_lt(r, c)
      +g = Sr.rr.bit(x, b)
      %rr.bit_eq(x, b) : {g <> Sr.rr.give(t, r, Nat.sub(b, g)) == _ <> DocSearch.ds_round(t, r, Nat.sub(b, _)) : List<&2, Nat>}
      %rr.give_eq(t, r, Nat.sub(b, g)) : {g <> Sr.rr.give(t, r, Nat.sub(b, g)) == g <> _ : List<&2, Nat>}
      {==}

def rr.zero_round(cs: List<&2, Nat>, +r: Nat) -> {Sr.rr.zeros(cs) == DocSearch.ds_round(cs, r, 0n) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      %rr.zero_round(t, r) : {0n <> Sr.rr.zeros(t) == 0n <> _ : List<&2, Nat>}
      {==}

def rr.plus_zeros(cs: List<&2, Nat>) -> {Sr.rr.zeros(cs) == DocSearch.ds_plus(Sr.rr.zeros(cs), Sr.rr.zeros(cs)) : List<&2, Nat>}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      %rr.plus_zeros(t) : {0n <> Sr.rr.zeros(t) == 0n <> _ : List<&2, Nat>}
      {==}

def rr.plus_eq(xs: List<&2, Nat>, ys: List<&2, Nat>) -> {Sr.rr.add(xs, ys) == DocSearch.ds_plus(xs, ys) : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      match ys:
        case Nil{}:
          {==}
        case +y <> u:
          %rr.plus_eq(t, u) : {Nat.add(x, y) <> Sr.rr.add(t, u) == Nat.add(x, y) <> _ : List<&2, Nat>}
          {==}

# with no budget, the spec's rounds keep nothing
def rr.spent(f: Nat, +cs: List<&2, Nat>, +r: Nat) -> {Sr.rr.zeros(cs) == DocSearch.ds_rounds(f, cs, r, 0n) : List<&2, Nat>}:
  match f:
    case 0n:
      rr.zero_round(cs, r)
    case 1n+g:
      +z = DocSearch.ds_round(cs, r, 0n)
      %rr.zero_round(cs, r) : {Sr.rr.zeros(cs) == DocSearch.ds_plus(_, DocSearch.ds_rounds(g, cs, 1n+r, Nat.sub(0n, DocSearch.ds_sum(z)))) : List<&2, Nat>}
      %rr.spent(g, cs, 1n+r) : {Sr.rr.zeros(cs) == DocSearch.ds_plus(Sr.rr.zeros(cs), _) : List<&2, Nat>}
      rr.plus_zeros(cs)

def rr.go_eq(f: Nat, +cs: List<&2, Nat>, +r: Nat, +b: Nat) -> {Sr.rr.go(f, cs, r, b) == DocSearch.ds_rounds(f, cs, r, b) : List<&2, Nat>}:
  match f:
    case 0n:
      match b:
        case 0n:
          rr.zero_round(cs, r)
        case 1n+c:
          rr.zero_round(cs, r)
    case 1n++g:
      match b:
        case 0n:
          rr.spent(1n+g, cs, r)
        case 1n+c:
          +gv = Sr.rr.give(cs, r, 1n+c)
          +b2 = Nat.sub(1n+c, Sr.sum(gv))
          %rr.give_eq(cs, r, 1n+c) : {Sr.rr.add(gv, Sr.rr.go(g, cs, 1n+r, b2)) == DocSearch.ds_plus(_, DocSearch.ds_rounds(g, cs, 1n+r, Nat.sub(1n+c, DocSearch.ds_sum(_)))) : List<&2, Nat>}
          %LADocSearch.ds.sum(gv) : {Sr.rr.add(gv, Sr.rr.go(g, cs, 1n+r, b2)) == DocSearch.ds_plus(gv, DocSearch.ds_rounds(g, cs, 1n+r, Nat.sub(1n+c, _))) : List<&2, Nat>}
          %rr.go_eq(g, cs, 1n+r, b2) : {Sr.rr.add(gv, Sr.rr.go(g, cs, 1n+r, b2)) == DocSearch.ds_plus(gv, _) : List<&2, Nat>}
          rr.plus_eq(gv, Sr.rr.go(g, cs, 1n+r, b2))

def rr.top_eq(xs: List<&2, Nat>) -> {Sr.rr.top(xs) == DocSearch.ds_top(xs) : Nat}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %rr.top_eq(t) : {Nat.max(x, Sr.rr.top(t)) == Nat.max(x, _) : Nat}
      {==}

def rr.ok_parts(+f: Nat, +cs: List<&2, Nat>, +r: Nat, +b: Nat, +d: Nat, e: {True{} == Sr.rr.ok(f, cs, r, b, d) : Bool}) -> {Bool.and(Nat.is_le(d, f), Bool.and(Nat.is_le(Nat.mul(d, Sr.rr.act(cs, r)), b), Sr.rr.clear(cs, r, d))) == True{} : Bool}:
  +hm = Nat.is_le(Nat.mul(d, Sr.rr.act(cs, r)), b)
  +rest = Bool.and(Nat.is_le(d, f), Bool.and(hm, Sr.rr.clear(cs, r, d)))
  LARrJump.rj.and_r(Nat.is_lt(0n, d), rest, Equal.sym(Bool, True{}, Sr.rr.ok(f, cs, r, b, d), e))

# the jumping rounds are the spec's rounds
def rr.fast_eq(fuel: Nat, ok: Bool, +f: Nat, +cs: List<&2, Nat>, +r: Nat, +b: Nat, +d: Nat, e: {ok == Sr.rr.ok(f, cs, r, b, d) : Bool}) -> {Sr.rr.fast(fuel, ok, f, cs, r, b, d) == DocSearch.ds_rounds(f, cs, r, b) : List<&2, Nat>}:
  match fuel:
    case 0n:
      rr.go_eq(f, cs, r, b)
    case 1n++k:
      match ok:
        case False{}:
          rr.go_eq(f, cs, r, b)
        case True{}:
          +a = Sr.rr.act(cs, r)
          +hm = Nat.is_le(Nat.mul(d, a), b)
          +cl = Sr.rr.clear(cs, r, d)
          +parts = rr.ok_parts(f, cs, r, b, d, e)
          +hd = LARrJump.rj.and_l(Nat.is_le(d, f), Bool.and(hm, cl), parts)
          +two = LARrJump.rj.and_r(Nat.is_le(d, f), Bool.and(hm, cl), parts)
          +f2 = Nat.sub(f, d)
          +r2 = Nat.add(r, d)
          +b2 = Nat.sub(b, Nat.mul(d, a))
          +d2 = Sr.rr.jump(f2, cs, r2, b2)
          +blk = Sr.rr.block(cs, r, d)
          +fast = Sr.rr.fast(k, Sr.rr.ok(f2, cs, r2, b2, d2), f2, cs, r2, b2, d2)
          %Equal.sym(List<&2, Nat>, Sr.rr.add(blk, fast), DocSearch.ds_plus(blk, fast), rr.plus_eq(blk, fast)) : {_ == DocSearch.ds_rounds(f, cs, r, b) : List<&2, Nat>}
          %Equal.sym(List<&2, Nat>, fast, DocSearch.ds_rounds(f2, cs, r2, b2), rr.fast_eq(k, Sr.rr.ok(f2, cs, r2, b2, d2), f2, cs, r2, b2, d2, {==})) : {DocSearch.ds_plus(blk, _) == DocSearch.ds_rounds(f, cs, r, b) : List<&2, Nat>}
          Equal.sym(List<&2, Nat>, DocSearch.ds_rounds(f, cs, r, b), DocSearch.ds_plus(blk, DocSearch.ds_rounds(f2, cs, r2, b2)), LARrJump.rj.jump(d, f, cs, r, b, hd, LARrJump.rj.and_l(hm, cl, two), LARrJump.rj.and_r(hm, cl, two)))

def DocSearch.limit_round_robin(cs, l):
  +f = Sr.rr.top(cs)
  +d = Sr.rr.jump(f, cs, 0n, l)
  %rr.top_eq(cs) : {Sr.rr(cs, l) == DocSearch.ds_rounds(_, cs, 0n, l) : List<&2, Nat>}
  rr.fast_eq(2n+List.length(&2, Nat, cs), Sr.rr.ok(f, cs, 0n, l, d), f, cs, 0n, l, d, {==})
