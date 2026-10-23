# eukhe: the proof of LAW tui_roles_resolve

import Base
import ../../bend/color.bend as Co
import ../../bend/theme.bend as T
import ../../bend/tui_color.bend as TC
import ../../laws/theme.bend as Theme
import ../base/bool/and.bend as LBoolAnd
import ../base/bool/misc.bend as LBoolMisc
import ../base/nat/is_lt.bend as LNatIsLt
import ./base.bend as LA

def pu.and_l(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      LBoolMisc.pu.absurd_ft({False{} == True{} : Bool}, h)

def pu.and_r(+a: Bool, +b: Bool, +h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      LBoolMisc.pu.absurd_ft({b == True{} : Bool}, h)

# The roles
# ---------

def pu.fill_len(+cols: List<&2, T.Ent>, +bg: Co.Rgb, +ts: List<&2, U32>) -> {List.length(&2, Maybe<&2, T.Val>, T.fill.map(cols, bg, ts)) == List.length(&2, U32, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, rest}:
      %pu.fill_len(cols, bg, rest) : {1n+List.length(&2, Maybe<&2, T.Val>, T.fill.map(cols, bg, rest)) == 1n+_ : Nat}
      {==}

def pu.all_lt(rs: List<&2, Nat>, +n: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, rest}:
      Bool.and(Nat.is_lt(r, n), pu.all_lt(rest, n))

# a complete palette has a value at every index below its length
def pu.get_found(+p: List<&2, Maybe<&2, T.Val>>, +r: Nat, +hc: {T.complete(p) == True{} : Bool}, +hl: {Nat.is_lt(r, List.length(&2, Maybe<&2, T.Val>, p)) == True{} : Bool})
  -> {TC.found(T.Val, List.get(&2, Maybe<&2, T.Val>, p, r)) == True{} : Bool}:
  match p r:
    case Nil{} q:
      LBoolMisc.pu.absurd_ft({TC.found(T.Val, List.get(&2, Maybe<&2, T.Val>, Nil{}, q)) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(q, 0n), True{}, LNatIsLt.pu.lt_zero_f(q), hl))
    case Con{+v, +rest} 0n:
      pu.and_l(Maybe.is_some(&2, T.Val, v), T.complete(rest), hc)
    case Con{+v, +rest} 1n+q:
      pu.get_found(rest, q, pu.and_r(Maybe.is_some(&2, T.Val, v), T.complete(rest), hc), hl)

def pu.resolves_go(+p: List<&2, Maybe<&2, T.Val>>, +rs: List<&2, Nat>, +hc: {T.complete(p) == True{} : Bool}, +hl: {pu.all_lt(rs, List.length(&2, Maybe<&2, T.Val>, p)) == True{} : Bool})
  -> {TC.resolves(p, rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      +len = List.length(&2, Maybe<&2, T.Val>, p)
      +here = pu.get_found(p, r, hc, pu.and_l(Nat.is_lt(r, len), pu.all_lt(rest, len), hl))
      +more = pu.resolves_go(p, rest, hc, pu.and_r(Nat.is_lt(r, len), pu.all_lt(rest, len), hl))
      LBoolAnd.pu.and_t(TC.found(T.Val, List.get(&2, Maybe<&2, T.Val>, p, r)), TC.resolves(p, rest), here, more)

def tui_roles_resolve(+f: T.Th, +v: {T.valid(f) == True{} : Bool}) -> {TC.resolves(T.palette(f), TC.roles()) == True{} : Bool}:
  match f:
    case T.Th{name, cols, page, card, info}:
      +bg = T.background(cols, page)
      +p = T.fill.map(cols, bg, T.toks())
      +hc = LA.theme_tokens_complete(T.Th{name, cols, page, card, info}, v)
      +hl = {%Equal.sym(Nat, List.length(&2, Maybe<&2, T.Val>, p), List.length(&2, U32, T.toks()), pu.fill_len(cols, bg, T.toks())) : {pu.all_lt(TC.roles(), _) == True{} : Bool}; {==} : {pu.all_lt(TC.roles(), List.length(&2, Maybe<&2, T.Val>, p)) == True{} : Bool}}
      pu.resolves_go(p, TC.roles(), hc, hl)

def Theme.tui_roles_resolve(f, v):
  tui_roles_resolve(f, v)
