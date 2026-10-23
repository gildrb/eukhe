# eukhe: lemmas the proofs of two or more areas share: pair

import Base
import ../../bend/tree.bend as Tr
import ./bool.bend as LBool
import ./logic/bool.bend as LLogicBool
import ./logic/list.bend as LLogicList
import ./logic/logic.bend as LLogicLogic
import ./logic/nat.bend as LLogicNat
import ./nat.bend as LNat

def wn_dm_fst(n: Nat, +m: Nat, -d: Nat, +r: Nat) ->
  {Pair.fst(Nat, Nat, Nat.divmod.go(n, m, 1n+d, r)) == 1n+Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          wn_dm_fst(np, r, 1n+d, 0n)
        case 1n+mp:
          wn_dm_fst(np, mp, d, 1n+r)

def wn_dm_snd(n: Nat, +m: Nat, -d: Nat, +r: Nat) ->
  {Pair.snd(Nat, Nat, Nat.divmod.go(n, m, 1n+d, r)) == Pair.snd(Nat, Nat, Nat.divmod.go(n, m, d, r)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+np:
      match m:
        case 0n:
          wn_dm_snd(np, r, 1n+d, 0n)
        case 1n+mp:
          wn_dm_snd(np, mp, d, 1n+r)

def wn_div_step(n: Nat) -> {Nat.div(10n+n, 10n) == 1n+Nat.div(n, 10n) : Nat}:
  wn_dm_fst(n, 9n, 0n, 0n)

def wn_mod_step(n: Nat) -> {Nat.mod(10n+n, 10n) == Nat.mod(n, 10n) : Nat}:
  wn_dm_snd(n, 9n, 0n, 0n)

def wn_mod_lt(+n: Nat) -> {LLogicBool.wn_lt10(Nat.mod(n, 10n)) == True{} : Bool}:
  match n:
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
      %Equal.sym(Nat, Nat.mod(10n+p, 10n), Nat.mod(p, 10n), wn_mod_step(p)) : {LLogicBool.wn_lt10(_) == True{} : Bool}
      wn_mod_lt(p)

# n == n % 10 + 10 * (n / 10)
def wn_dm(+n: Nat) -> {Nat.add(Nat.mod(n, 10n), Nat.mul(10n, Nat.div(n, 10n))) == n : Nat}:
  match n:
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
      %Equal.sym(Nat, Nat.mod(10n+p, 10n), Nat.mod(p, 10n), wn_mod_step(p)) : {Nat.add(_, Nat.mul(10n, Nat.div(10n+p, 10n))) == 10n+p : Nat}
      %Equal.sym(Nat, Nat.div(10n+p, 10n), 1n+Nat.div(p, 10n), wn_div_step(p)) : {Nat.add(Nat.mod(p, 10n), Nat.mul(10n, _)) == 10n+p : Nat}
      %Equal.sym(Nat, Nat.mul(10n, 1n+Nat.div(p, 10n)), Nat.add(10n, Nat.mul(10n, Nat.div(p, 10n))), LNat.wn_mul_succ_r(10n, Nat.div(p, 10n))) : {Nat.add(Nat.mod(p, 10n), _) == 10n+p : Nat}
      %Equal.sym(Nat, Nat.add(Nat.mod(p, 10n), Nat.add(10n, Nat.mul(10n, Nat.div(p, 10n)))), Nat.add(10n, Nat.add(Nat.mod(p, 10n), Nat.mul(10n, Nat.div(p, 10n)))), LNat.wn_add_swap(Nat.mod(p, 10n), 10n, Nat.mul(10n, Nat.div(p, 10n)))) : {_ == 10n+p : Nat}
      Equal.cong(Nat, Nat, k => 10n+k, Nat.add(Nat.mod(p, 10n), Nat.mul(10n, Nat.div(p, 10n))), p, wn_dm(p))

# (1 + p) / 10 <= p
def wn_div_lt(+p: Nat) -> {Nat.is_le(Nat.div(1n+p, 10n), p) == True{} : Bool}:
  match p:
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
    case 10n+q:
      %Equal.sym(Nat, Nat.div(11n+q, 10n), 1n+Nat.div(1n+q, 10n), wn_div_step(1n+q)) : {Nat.is_le(_, 10n+q) == True{} : Bool}
      LNat.wn_le_add(9n, Nat.div(1n+q, 10n), q, wn_div_lt(q))

def wn_div_le(+n: Nat) -> {Nat.is_le(Nat.div(n, 10n), n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      LNat.wn_le_step(Nat.div(1n+p, 10n), p, wn_div_lt(p))

# n / 10 == 0 gives n % 10 == n
def wn_dm0(+n: Nat, e: {Nat.div(n, 10n) == 0n : Nat}) -> {Nat.mod(n, 10n) == n : Nat}:
  %LNat.wn_add_zero_r(Nat.mod(n, 10n)) : {_ == n : Nat}
  %e : {Nat.add(Nat.mod(n, 10n), Nat.mul(10n, _)) == n : Nat}
  wn_dm(n)

def wn_vl(+g: Nat, +q: Nat, h: {Nat.is_le(q, g) == True{} : Bool}) -> {LLogicNat.wo_value(LLogicList.wn_L(g, q)) == q : Nat}:
  match g q:
    case 0n 0n:
      {==}
    case 0n 1n+p:
      LLogicLogic.wn_absurd({LLogicNat.wo_value(LLogicList.wn_L(0n, 1n+p)) == 1n+p : Nat}, h)
    case 1n+f 0n:
      {==}
    case 1n+f 1n+p:
      %Equal.sym(Nat, LLogicNat.wo_value(LLogicList.wn_L(f, Nat.div(1n+p, 10n))), Nat.div(1n+p, 10n), wn_vl(f, Nat.div(1n+p, 10n), LNat.wn_le_trans(Nat.div(1n+p, 10n), p, f, wn_div_lt(p), h))) : {Nat.add(Nat.mod(1n+p, 10n), Nat.mul(10n, _)) == 1n+p : Nat}
      wn_dm(1n+p)

# the digits of n are worth n
def wn_vf(+n: Nat) -> {LLogicNat.wo_value(LLogicList.wn_full(n)) == n : Nat}:
  %Equal.sym(Nat, LLogicNat.wo_value(LLogicList.wn_L(n, Nat.div(n, 10n))), Nat.div(n, 10n), wn_vl(n, Nat.div(n, 10n), wn_div_le(n))) : {Nat.add(Nat.mod(n, 10n), Nat.mul(10n, _)) == n : Nat}
  wn_dm(n)

def wn_okh(r: Nat, f: Nat, +q: Nat, er: {Nat.div(1n+q, 10n) == r : Nat}, hf: {Nat.is_le(r, f) == True{} : Bool},
  rec: @q2: Nat -> @d2: Nat -> {LLogicBool.wn_lt10(d2) == True{} : Bool} -> {Nat.is_le(1n+q2, f) == True{} : Bool}
    -> {LLogicBool.wn_okc(LLogicList.wn_L(f, 1n+q2), d2) == True{} : Bool})
  -> {LLogicBool.wn_okc(LLogicList.wn_L(f, r), Nat.mod(1n+q, 10n)) == True{} : Bool}:
  match r:
    case 0n:
      +em = wn_dm0(1n+q, er)
      %Equal.sym(List<&2, Nat>, LLogicList.wn_L(f, 0n), Nil{}, LLogicList.wn_Lzero(f)) : {LLogicBool.wn_okc(_, Nat.mod(1n+q, 10n)) == True{} : Bool}
      %Equal.sym(Nat, Nat.mod(1n+q, 10n), 1n+q, em) : {LLogicBool.wn_nz10(_) == True{} : Bool}
      %em : {LLogicBool.wn_lt10(_) == True{} : Bool}
      wn_mod_lt(1n+q)
    case 1n+r2:
      rec(r2, Nat.mod(1n+q, 10n), wn_mod_lt(1n+q), hf)

def wn_okL(+g: Nat) -> @q: Nat -> @d: Nat -> {LLogicBool.wn_lt10(d) == True{} : Bool} -> {Nat.is_le(1n+q, g) == True{} : Bool}
  -> {LLogicBool.wn_okc(LLogicList.wn_L(g, 1n+q), d) == True{} : Bool}:
  match g:
    case 0n:
      q => d => hd => hg => LLogicLogic.wn_absurd({LLogicBool.wn_okc(LLogicList.wn_L(0n, 1n+q), d) == True{} : Bool}, hg)
    case 1n+f:
      +q => d => hd => hg =>
        LBool.wn_and_intro(LLogicBool.wn_lt10(d), LLogicBool.wn_okc(LLogicList.wn_L(f, Nat.div(1n+q, 10n)), Nat.mod(1n+q, 10n)), hd,
          wn_okh(Nat.div(1n+q, 10n), f, q, {==}, LNat.wn_le_trans(Nat.div(1n+q, 10n), q, f, wn_div_lt(q), hg), wn_okL(f)))

# the digits of a positive n are canonical
def wn_cf(+p: Nat) -> {LLogicBool.wn_canon(LLogicList.wn_full(1n+p)) == True{} : Bool}:
  wn_okh(Nat.div(1n+p, 10n), 1n+p, p, {==}, wn_div_le(1n+p), wn_okL(1n+p))

def tc.keep_case_bst(b: Bool, +m: Tr.KMap, +n: Tr.KMap, +bm: {LLogicBool.tc.bst(m) == True{} : Bool}, +bn: {LLogicBool.tc.bst(n) == True{} : Bool}) -> {LLogicBool.tc.bst(Pair.fst(Tr.KMap, Tr.Ans, Tr.keep.ans(b, m, n))) == True{} : Bool}:
  match b:
    case True{}:
      bn
    case False{}:
      bm
