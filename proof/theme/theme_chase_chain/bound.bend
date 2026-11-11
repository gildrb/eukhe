# eukhe: lemmas of LAW theme_chase_chain: a chain is no longer than the
# variables (cb.chain_fits)
#
# Every variable a chain that decides goes through exists (its value is
# read: cb.next_var), so its index is below the number of variables
# (cb.get_lt); and no variable repeats (th.fresh). So the variables of the
# chain are distinct indices below the count: at most the count of them.
# The count is kept as cb.cnt(met, l): the indices below l not in met;
# a fresh index below l leaves one fewer (cb.cnt_drop), no index met
# leaves all l (cb.cnt_nil).

import Base
import ../../../bend/theme/file.bend as TFile
import ../../../bend/theme/chase.bend as TChase
import ../../../laws/theme.bend as Theme
import ../base.bend as LA

# Counting the indices not met
# ----------------------------

def cb.cnt.step(b: Bool, c: Nat) -> Nat:
  match b:
    case True{}:
      c
    case False{}:
      1n+c

# the indices below l that are not in met
def cb.cnt(+met: List<&2, Nat>, l: Nat) -> Nat:
  match l:
    case 0n:
      0n
    case 1n++k:
      cb.cnt.step(Theme.th.mem(met, k), cb.cnt(met, k))

# with nothing met, every index below l counts
def cb.cnt_nil(l: Nat) -> {cb.cnt(Nil{}, l) == l : Nat}:
  match l:
    case 0n:
      {==}
    case 1n++k:
      Equal.cong(Nat, Nat, x => 1n+x, cb.cnt(Nil{}, k), k, cb.cnt_nil(k))

# 1 + k <= i: i is not k
def cb.le_ne(i: Nat, k: Nat, h: {Nat.is_le(1n+k, i) == True{} : Bool}) -> {Nat.is_eq(i, k) == False{} : Bool}:
  match i k:
    case 0n 0n:
      LA.themes.pt.absurdF({Nat.is_eq(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      LA.themes.pt.absurdF({Nat.is_eq(0n, 1n+q) == False{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      cb.le_ne(p, q, h)

# 1 + k <= i: k <= i
def cb.le_pred(k: Nat, i: Nat, h: {Nat.is_le(1n+k, i) == True{} : Bool}) -> {Nat.is_le(k, i) == True{} : Bool}:
  match k i:
    case 0n 0n:
      {==}
    case 0n 1n+p:
      {==}
    case 1n+q 0n:
      LA.themes.pt.absurdF({Nat.is_le(1n+q, 0n) == True{} : Bool}, h)
    case 1n+q 1n+p:
      cb.le_pred(q, p, h)

def cb.lt_zero(i: Nat, h: {Nat.is_lt(i, 0n) == True{} : Bool}) -> {False{} == True{} : Bool}:
  match i:
    case 0n:
      h
    case 1n+p:
      h

# an index at or past l changes no count below l
def cb.cnt_above(+i: Nat, +met: List<&2, Nat>, l: Nat, +h: {Nat.is_le(l, i) == True{} : Bool}) -> {cb.cnt(i <> met, l) == cb.cnt(met, l) : Nat}:
  match l:
    case 0n:
      {==}
    case 1n++k:
      %Equal.sym(Bool, Nat.is_eq(i, k), False{}, cb.le_ne(i, k, h)) : {cb.cnt.step(Bool.or(_, Theme.th.mem(met, k)), cb.cnt(i <> met, k)) == cb.cnt.step(Theme.th.mem(met, k), cb.cnt(met, k)) : Nat}
      %Equal.sym(Nat, cb.cnt(i <> met, k), cb.cnt(met, k), cb.cnt_above(i, met, k, cb.le_pred(k, i, h))) : {cb.cnt.step(Theme.th.mem(met, k), _) == cb.cnt.step(Theme.th.mem(met, k), cb.cnt(met, k)) : Nat}
      {==}

# Nat.is_eq says the two are equal
def cb.eq(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LA.themes.pt.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LA.themes.pt.absurdF({1n+p == 0n : Nat}, h)
    case 1n++p 1n++q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, cb.eq(p, q, h))

# i < 1 + k and i is not k: i < k
def cb.lt_ne(i: Nat, k: Nat, hl: {Nat.is_lt(i, 1n+k) == True{} : Bool}, hn: {Nat.is_eq(i, k) == False{} : Bool}) -> {Nat.is_lt(i, k) == True{} : Bool}:
  match i k:
    case 0n 0n:
      LA.themes.pt.absurdT({Nat.is_lt(0n, 0n) == True{} : Bool}, hn)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      LA.themes.pt.absurdF({Nat.is_lt(1n+p, 0n) == True{} : Bool}, cb.lt_zero(p, hl))
    case 1n+p 1n+q:
      cb.lt_ne(p, q, hl, hn)

def cb.le_refl(i: Nat) -> {Nat.is_le(i, i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      cb.le_refl(p)

def cb.eq_refl(i: Nat) -> {Nat.is_eq(i, i) == True{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+p:
      cb.eq_refl(p)

# the step of the count at index k, met or not: what a met index drops
def cb.drop.step(b: Bool, -c: Nat, -d: Nat, ih: {c == 1n+d : Nat}) -> {cb.cnt.step(b, c) == 1n+cb.cnt.step(b, d) : Nat}:
  match b:
    case True{}:
      ih
    case False{}:
      Equal.cong(Nat, Nat, x => 1n+x, c, 1n+d, ih)

# at index k = i: i counts with met, not with i <> met
def cb.drop.here(+i: Nat, +met: List<&2, Nat>, hm: {Theme.th.mem(met, i) == False{} : Bool}) -> {cb.cnt(met, 1n+i) == 1n+cb.cnt(i <> met, 1n+i) : Nat}:
  +same = cb.cnt_above(i, met, i, cb.le_refl(i))
  %Equal.sym(Bool, Theme.th.mem(met, i), False{}, hm) : {cb.cnt.step(_, cb.cnt(met, i)) == 1n+cb.cnt.step(Bool.or(Nat.is_eq(i, i), Theme.th.mem(met, i)), cb.cnt(i <> met, i)) : Nat}
  %Equal.sym(Bool, Nat.is_eq(i, i), True{}, cb.eq_refl(i)) : {1n+cb.cnt(met, i) == 1n+cb.cnt.step(Bool.or(_, Theme.th.mem(met, i)), cb.cnt(i <> met, i)) : Nat}
  Equal.cong(Nat, Nat, x => 1n+x, cb.cnt(met, i), cb.cnt(i <> met, i), Equal.sym(Nat, cb.cnt(i <> met, i), cb.cnt(met, i), same))

# k = i, or i below k with what the count drops there (ih)
def cb.drop.at(same: Bool, +i: Nat, +met: List<&2, Nat>, +k: Nat, +hs: {Nat.is_eq(i, k) == same : Bool}, hl: {Nat.is_lt(i, 1n+k) == True{} : Bool}, hm: {Theme.th.mem(met, i) == False{} : Bool}, ih: {Nat.is_lt(i, k) == True{} : Bool} -> {cb.cnt(met, k) == 1n+cb.cnt(i <> met, k) : Nat}) -> {cb.cnt(met, 1n+k) == 1n+cb.cnt(i <> met, 1n+k) : Nat}:
  match same:
    case True{}:
      %cb.eq(i, k, hs) : {cb.cnt(met, 1n+_) == 1n+cb.cnt(i <> met, 1n+_) : Nat}
      cb.drop.here(i, met, hm)
    case False{}:
      +drop = ih(cb.lt_ne(i, k, hl, hs))
      %Equal.sym(Bool, Nat.is_eq(i, k), False{}, hs) : {cb.cnt.step(Theme.th.mem(met, k), cb.cnt(met, k)) == 1n+cb.cnt.step(Bool.or(_, Theme.th.mem(met, k)), cb.cnt(i <> met, k)) : Nat}
      cb.drop.step(Theme.th.mem(met, k), cb.cnt(met, k), cb.cnt(i <> met, k), drop)

# a fresh index below l: the count without it is one more than with it
def cb.cnt_drop(+i: Nat, +met: List<&2, Nat>, l: Nat, hl: {Nat.is_lt(i, l) == True{} : Bool}, +hm: {Theme.th.mem(met, i) == False{} : Bool}) -> {cb.cnt(met, l) == 1n+cb.cnt(i <> met, l) : Nat}:
  match l:
    case 0n:
      LA.themes.pt.absurdF({cb.cnt(met, 0n) == 1n+cb.cnt(i <> met, 0n) : Nat}, cb.lt_zero(i, hl))
    case 1n++k:
      cb.drop.at(Nat.is_eq(i, k), i, met, k, {==}, hl, hm, h => cb.cnt_drop(i, met, k, h, hm))

# The variables of a chain exist
# ------------------------------

def cb.at_var(same: Bool, +vars: List<&2, TFile.Var>, +i: Nat, -v: TFile.Json, h: {Theme.th.next.at(same, vars, i) == Some{v} : Maybe<&2, TFile.Json>}) -> {Theme.th.var(vars, i) == Some{v} : Maybe<&2, TFile.Json>}:
  match same:
    case True{}:
      h
    case False{}:
      LA.pt.none_some(TFile.Json, v, {Theme.th.var(vars, i) == Some{v} : Maybe<&2, TFile.Json>}, h)

def cb.str_var(r: Bool, +vars: List<&2, TFile.Var>, at: Maybe<&2, Nat>, +i: Nat, -v: TFile.Json, h: {Theme.th.next.str(r, vars, at, i) == Some{v} : Maybe<&2, TFile.Json>}) -> {Theme.th.var(vars, i) == Some{v} : Maybe<&2, TFile.Json>}:
  match r:
    case True{}:
      match at:
        case None{}:
          LA.pt.none_some(TFile.Json, v, {Theme.th.var(vars, i) == Some{v} : Maybe<&2, TFile.Json>}, h)
        case Some{k}:
          cb.at_var(Nat.is_eq(k, i), vars, i, v, h)
    case False{}:
      LA.pt.none_some(TFile.Json, v, {Theme.th.var(vars, i) == Some{v} : Maybe<&2, TFile.Json>}, h)

# the value a chain steps to is the value of its variable
def cb.next_var(+vars: List<&2, TFile.Var>, j: TFile.Json, +i: Nat, -v: TFile.Json, h: {Theme.th.next(vars, j, i) == Some{v} : Maybe<&2, TFile.Json>}) -> {Theme.th.var(vars, i) == Some{v} : Maybe<&2, TFile.Json>}:
  match j:
    case TFile.JStr{s, at}:
      cb.str_var(Theme.th.refers(s), vars, at, i, v, h)
    case TFile.JNum{t}:
      LA.pt.none_some(TFile.Json, v, {Theme.th.var(vars, i) == Some{v} : Maybe<&2, TFile.Json>}, h)
    case TFile.JOther{t}:
      LA.pt.none_some(TFile.Json, v, {Theme.th.var(vars, i) == Some{v} : Maybe<&2, TFile.Json>}, h)

# a variable that has a value has an index below the count
def cb.get_lt(xs: List<&2, TFile.Var>, i: Nat, -v: TFile.Json, h: {Theme.th.var(xs, i) == Some{v} : Maybe<&2, TFile.Json>}) -> {Nat.is_lt(i, List.length(&2, TFile.Var, xs)) == True{} : Bool}:
  match xs i:
    case Nil{} _:
      LA.pt.none_some(TFile.Json, v, {Nat.is_lt(i, 0n) == True{} : Bool}, h)
    case x <> rest 0n:
      {==}
    case x <> rest 1n+p:
      cb.get_lt(rest, p, v, h)

# The bound
# ---------

def cb.if_rest(m: Maybe<&2, TFile.Json>, -r: Maybe<&2, TChase.Got>, -g: TChase.Got, h: {Theme.th.chain.if(m, r) == Some{g} : Maybe<&2, TChase.Got>}) -> {r == Some{g} : Maybe<&2, TChase.Got>}:
  match m:
    case None{}:
      LA.pt.none_some(TChase.Got, g, {r == Some{g} : Maybe<&2, TChase.Got>}, h)
    case Some{x}:
      h

def cb.if_some(m: Maybe<&2, TFile.Json>, -r: Maybe<&2, TChase.Got>, -g: TChase.Got, h: {Theme.th.chain.if(m, r) == Some{g} : Maybe<&2, TChase.Got>}) -> {m == Some{Theme.th.or.json(m)} : Maybe<&2, TFile.Json>}:
  match m:
    case None{}:
      LA.pt.none_some(TChase.Got, g, {None{} == Some{Theme.th.or.json(None{})} : Maybe<&2, TFile.Json>}, h)
    case Some{x}:
      {==}

def cb.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, False{}, True{}, h)
    case False{}:
      {==}

def cb.le0(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a chain from met that decides, fresh over met, is no longer than the
# indices below the count of the variables that met has not taken
def cb.chain(p: List<&2, Nat>, +vars: List<&2, TFile.Var>, +met: List<&2, Nat>, +j: TFile.Json, +g: TChase.Got, +hd: {Theme.th.fresh(p, met) == True{} : Bool}, +he: {Theme.th.chain(p, vars, met, j) == Some{g} : Maybe<&2, TChase.Got>}) -> {Nat.is_le(List.length(&2, Nat, p), cb.cnt(met, List.length(&2, TFile.Var, vars))) == True{} : Bool}:
  match p:
    case Nil{}:
      cb.le0(cb.cnt(met, List.length(&2, TFile.Var, vars)))
    case Con{+i, +rest}:
      +l = List.length(&2, TFile.Var, vars)
      +m = Theme.th.next(vars, j, i)
      +hm = cb.not_t(Theme.th.mem(met, i), LA.themes.pt.and_l(Bool.not(Theme.th.mem(met, i)), Theme.th.fresh(rest, i <> met), hd))
      +hd2 = LA.themes.pt.and_r(Bool.not(Theme.th.mem(met, i)), Theme.th.fresh(rest, i <> met), hd)
      +hr = cb.if_rest(m, Theme.th.chain(rest, vars, i <> met, Theme.th.or.json(m)), g, he)
      +hv = cb.if_some(m, Theme.th.chain(rest, vars, i <> met, Theme.th.or.json(m)), g, he)
      +hl = cb.get_lt(vars, i, Theme.th.or.json(m), cb.next_var(vars, j, i, Theme.th.or.json(m), hv))
      %Equal.sym(Nat, cb.cnt(met, l), 1n+cb.cnt(i <> met, l), cb.cnt_drop(i, met, l, hl, hm)) : {Nat.is_le(1n+List.length(&2, Nat, rest), _) == True{} : Bool}
      cb.chain(rest, vars, i <> met, Theme.th.or.json(m), g, hd2, hr)

# LAW theme_chase_chain's bound: a chain that decides, no variable twice,
# is no longer than the variables
def cb.chain_fits(p: List<&2, Nat>, +vars: List<&2, TFile.Var>, +j: TFile.Json, +g: TChase.Got, hd: {Theme.th.fresh(p, Nil{}) == True{} : Bool}, he: {Theme.th.chain(p, vars, Nil{}, j) == Some{g} : Maybe<&2, TChase.Got>}) -> {Nat.is_le(List.length(&2, Nat, p), List.length(&2, TFile.Var, vars)) == True{} : Bool}:
  %cb.cnt_nil(List.length(&2, TFile.Var, vars)) : {Nat.is_le(List.length(&2, Nat, p), _) == True{} : Bool}
  cb.chain(p, vars, Nil{}, j, g, hd, he)
