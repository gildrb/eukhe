# eukhe: the proof of LAW tui_roles_resolve

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/token.bend as TToken
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

def pu.fill_len(+cols: List<&2, TFile.Ent>, +bg: Co.Rgb, +ts: List<&2, U32>) -> {List.length(&2, Maybe<&2, TFile.Val>, TPalette.fill.map(cols, bg, ts)) == List.length(&2, U32, ts) : Nat}:
  match ts:
    case Nil{}:
      {==}
    case Con{t, rest}:
      %pu.fill_len(cols, bg, rest) : {1n+List.length(&2, Maybe<&2, TFile.Val>, TPalette.fill.map(cols, bg, rest)) == 1n+_ : Nat}
      {==}

def pu.all_lt(rs: List<&2, Nat>, +n: Nat) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case Con{r, rest}:
      Bool.and(Nat.is_lt(r, n), pu.all_lt(rest, n))

# a complete palette has a value at every index below its length
def pu.get_found(+p: List<&2, Maybe<&2, TFile.Val>>, +r: Nat, +hc: {TPalette.complete(p) == True{} : Bool}, +hl: {Nat.is_lt(r, List.length(&2, Maybe<&2, TFile.Val>, p)) == True{} : Bool})
  -> {TC.found(TFile.Val, List.get(&2, Maybe<&2, TFile.Val>, p, r)) == True{} : Bool}:
  match p r:
    case Nil{} q:
      LBoolMisc.pu.absurd_ft({TC.found(TFile.Val, List.get(&2, Maybe<&2, TFile.Val>, Nil{}, q)) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(q, 0n), True{}, LNatIsLt.pu.lt_zero_f(q), hl))
    case Con{+v, +rest} 0n:
      pu.and_l(Maybe.is_some(&2, TFile.Val, v), TPalette.complete(rest), hc)
    case Con{+v, +rest} 1n+q:
      pu.get_found(rest, q, pu.and_r(Maybe.is_some(&2, TFile.Val, v), TPalette.complete(rest), hc), hl)

def pu.resolves_go(+p: List<&2, Maybe<&2, TFile.Val>>, +rs: List<&2, Nat>, +hc: {TPalette.complete(p) == True{} : Bool}, +hl: {pu.all_lt(rs, List.length(&2, Maybe<&2, TFile.Val>, p)) == True{} : Bool})
  -> {TC.resolves(p, rs) == True{} : Bool}:
  match rs:
    case Nil{}:
      {==}
    case Con{+r, +rest}:
      +len = List.length(&2, Maybe<&2, TFile.Val>, p)
      +here = pu.get_found(p, r, hc, pu.and_l(Nat.is_lt(r, len), pu.all_lt(rest, len), hl))
      +more = pu.resolves_go(p, rest, hc, pu.and_r(Nat.is_lt(r, len), pu.all_lt(rest, len), hl))
      LBoolAnd.pu.and_t(TC.found(TFile.Val, List.get(&2, Maybe<&2, TFile.Val>, p, r)), TC.resolves(p, rest), here, more)

def tui_roles_resolve(+f: TFile.Th, +v: {TToken.valid(f) == True{} : Bool}) -> {TC.resolves(TPalette.palette(f), TC.roles()) == True{} : Bool}:
  match f:
    case TFile.Th{name, cols, page, card, info}:
      +bg = TPalette.background(cols, page)
      +p = TPalette.fill.map(cols, bg, TToken.toks())
      +hc = LA.theme_tokens_complete(TFile.Th{name, cols, page, card, info}, v)
      +hl = {%Equal.sym(Nat, List.length(&2, Maybe<&2, TFile.Val>, p), List.length(&2, U32, TToken.toks()), pu.fill_len(cols, bg, TToken.toks())) : {pu.all_lt(TC.roles(), _) == True{} : Bool}; {==} : {pu.all_lt(TC.roles(), List.length(&2, Maybe<&2, TFile.Val>, p)) == True{} : Bool}}
      pu.resolves_go(p, TC.roles(), hc, hl)

def Theme.tui_roles_resolve(f, v):
  tui_roles_resolve(f, v)
