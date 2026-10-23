# eukhe: the proof of LAW theme_chase_rule

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/chase.bend as TChase
import ../../bend/theme/file.bend as TFile
import ../../laws/theme.bend as Theme
import ./base.bend as LA

# Values
# ------
# The model and the rule take the same steps: the seen check of a leaf
# is the membership, the variable lookup of a leaf the list lookup.

def pt.has_mem(xs: List<&2, Nat>, +i: Nat, hit: Bool) -> {TChase.seen.has(xs, i, hit) == Bool.or(hit, Theme.th.mem(xs, i)) : Bool}:
  match xs:
    case Nil{}:
      match hit:
        case True{}:
          {==}
        case False{}:
          {==}
    case Con{x, rest}:
      match hit:
        case True{}:
          {==}
        case False{}:
          pt.has_mem(rest, i, Nat.is_eq(x, i))

def pt.var_val(xs: List<&2, TFile.Var>, n: Nat) -> {TChase.var.val(xs, n) == Theme.th.var(xs, n) : Maybe<&2, TFile.Json>}:
  match xs n:
    case Nil{} q:
      {==}
    case Con{TFile.Var{nm, v}, rest} 0n:
      {==}
    case Con{x, rest} 1n+p:
      pt.var_val(rest, p)

def pt.hexgot(m: Maybe<&2, Co.Rgb>, s: String) -> {TChase.hex.got(m, s) == Theme.th.hex(m, s) : TChase.Got}:
  match m:
    case None{}:
      {==}
    case Some{c}:
      {==}

def pt.numgot(m: Maybe<&2, U32>, s: String) -> {TChase.num.got(m, s) == Theme.th.num(m, s) : TChase.Got}:
  match m:
    case None{}:
      {==}
    case Some{i}:
      {==}

# The indexed chase
# -----------------
# The variable tree answers as the list (pt.vt_at), the seen tree as the
# list of variables met (pt.st_sset), so each step over the trees is the
# rule's step (pt.look_step) and the walks agree for any fuel
# (pt.look_walk).

# below the split, the first h variables answer as all of them
def pt.val_take(xs: List<&2, TFile.Var>, +h: Nat, +i: Nat, lt: {Nat.is_lt(i, h) == True{} : Bool}) -> {TChase.var.val(List.take(&2, TFile.Var, xs, h), i) == TChase.var.val(xs, i) : Maybe<&2, TFile.Json>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case TFile.Var{nm, v}:
          match h:
            case 0n:
              match i:
                case 0n:
                  LA.themes.pt.absurdF({TChase.var.val(Nil{}, 0n) == TChase.var.val(TFile.Var{nm, v} <> rest, 0n) : Maybe<&2, TFile.Json>}, lt)
                case 1n+ip:
                  LA.themes.pt.absurdF({TChase.var.val(Nil{}, 1n+ip) == TChase.var.val(TFile.Var{nm, v} <> rest, 1n+ip) : Maybe<&2, TFile.Json>}, lt)
            case 1n+hp:
              match i:
                case 0n:
                  {==}
                case 1n+ip:
                  pt.val_take(rest, hp, ip, lt)

# from the split on, the variables past the first h answer as all of them
def pt.val_drop(xs: List<&2, TFile.Var>, +h: Nat, +i: Nat, ge: {Nat.is_lt(i, h) == False{} : Bool}) -> {TChase.var.val(List.drop(&2, TFile.Var, xs, h), Nat.sub(i, h)) == TChase.var.val(xs, i) : Maybe<&2, TFile.Json>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case TFile.Var{nm, v}:
          match h:
            case 0n:
              match i:
                case 0n:
                  {==}
                case 1n+ip:
                  {==}
            case 1n+hp:
              match i:
                case 0n:
                  LA.themes.pt.absurdT({TChase.var.val(List.drop(&2, TFile.Var, TFile.Var{nm, v} <> rest, 1n+hp), Nat.sub(0n, 1n+hp)) == TChase.var.val(TFile.Var{nm, v} <> rest, 0n) : Maybe<&2, TFile.Json>}, ge)
                case 1n+ip:
                  pt.val_drop(rest, hp, ip, ge)

def pt.vt_node(+h: Nat, +a: TChase.VT, +b: TChase.VT, +xs: List<&2, TFile.Var>, +i: Nat, c: Bool, e: {Nat.is_lt(i, h) == c : Bool},
  ia: {TChase.vt.at(a, i) == TChase.var.val(List.take(&2, TFile.Var, xs, h), i) : Maybe<&2, TFile.Json>},
  ib: {TChase.vt.at(b, Nat.sub(i, h)) == TChase.var.val(List.drop(&2, TFile.Var, xs, h), Nat.sub(i, h)) : Maybe<&2, TFile.Json>})
  -> {TChase.vt.get(TChase.VN{h, a, b}, c, i) == TChase.var.val(xs, i) : Maybe<&2, TFile.Json>}:
  match c:
    case True{}:
      Equal.trans(Maybe<&2, TFile.Json>, TChase.vt.at(a, i), TChase.var.val(List.take(&2, TFile.Var, xs, h), i), TChase.var.val(xs, i), ia, pt.val_take(xs, h, i, e))
    case False{}:
      Equal.trans(Maybe<&2, TFile.Json>, TChase.vt.at(b, Nat.sub(i, h)), TChase.var.val(List.drop(&2, TFile.Var, xs, h), Nat.sub(i, h)), TChase.var.val(xs, i), ib, pt.val_drop(xs, h, i, e))

# the tree of the variables answers as their list, whatever its splits
def pt.vt_build(fuel: Nat, small: Bool, +xs: List<&2, TFile.Var>, +n: Nat, +i: Nat) -> {TChase.vt.at(TChase.vt.build(fuel, small, xs, n), i) == TChase.var.val(xs, i) : Maybe<&2, TFile.Json>}:
  match fuel:
    case 0n:
      {==}
    case 1n++f:
      match small:
        case True{}:
          {==}
        case False{}:
          +h = Nat.div(n, 2n)
          +r = Nat.sub(n, h)
          +ta = List.take(&2, TFile.Var, xs, h)
          +tb = List.drop(&2, TFile.Var, xs, h)
          +a = TChase.vt.build(f, Nat.is_le(h, 1n), ta, h)
          +b = TChase.vt.build(f, Nat.is_le(r, 1n), tb, r)
          pt.vt_node(h, a, b, xs, i, Nat.is_lt(i, h), {==}, pt.vt_build(f, Nat.is_le(h, 1n), ta, h, i), pt.vt_build(f, Nat.is_le(r, 1n), tb, r, Nat.sub(i, h)))

# Nat facts on both sides of a split
def pt.split_lo_ne(+h: Nat, +a: Nat, +b: Nat, la: {Nat.is_lt(a, h) == True{} : Bool}, lb: {Nat.is_lt(b, h) == False{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match h:
    case 0n:
      match a:
        case 0n:
          LA.themes.pt.absurdF({Nat.is_eq(0n, b) == False{} : Bool}, la)
        case 1n+ap:
          LA.themes.pt.absurdF({Nat.is_eq(1n+ap, b) == False{} : Bool}, la)
    case 1n+hp:
      match a:
        case 0n:
          match b:
            case 0n:
              LA.themes.pt.absurdT({Nat.is_eq(0n, 0n) == False{} : Bool}, lb)
            case 1n+bp:
              {==}
        case 1n+ap:
          match b:
            case 0n:
              LA.themes.pt.absurdT({Nat.is_eq(1n+ap, 0n) == False{} : Bool}, lb)
            case 1n+bp:
              pt.split_lo_ne(hp, ap, bp, la, lb)

def pt.split_hi_ne(+h: Nat, +a: Nat, +b: Nat, la: {Nat.is_lt(a, h) == False{} : Bool}, lb: {Nat.is_lt(b, h) == True{} : Bool}) -> {Nat.is_eq(a, b) == False{} : Bool}:
  match h:
    case 0n:
      match b:
        case 0n:
          LA.themes.pt.absurdF({Nat.is_eq(a, 0n) == False{} : Bool}, lb)
        case 1n+bp:
          LA.themes.pt.absurdF({Nat.is_eq(a, 1n+bp) == False{} : Bool}, lb)
    case 1n+hp:
      match a:
        case 0n:
          LA.themes.pt.absurdT({Nat.is_eq(0n, b) == False{} : Bool}, la)
        case 1n+ap:
          match b:
            case 0n:
              {==}
            case 1n+bp:
              pt.split_hi_ne(hp, ap, bp, la, lb)

def pt.split_hi_eq(+h: Nat, +a: Nat, +b: Nat, la: {Nat.is_lt(a, h) == False{} : Bool}, lb: {Nat.is_lt(b, h) == False{} : Bool}) -> {Nat.is_eq(Nat.sub(a, h), Nat.sub(b, h)) == Nat.is_eq(a, b) : Bool}:
  match h:
    case 0n:
      match a:
        case 0n:
          match b:
            case 0n:
              {==}
            case 1n+bp:
              {==}
        case 1n+ap:
          match b:
            case 0n:
              {==}
            case 1n+bp:
              {==}
    case 1n+hp:
      match a:
        case 0n:
          LA.themes.pt.absurdT({Nat.is_eq(Nat.sub(0n, 1n+hp), Nat.sub(b, 1n+hp)) == Nat.is_eq(0n, b) : Bool}, la)
        case 1n+ap:
          match b:
            case 0n:
              LA.themes.pt.absurdT({Nat.is_eq(Nat.sub(1n+ap, 1n+hp), Nat.sub(0n, 1n+hp)) == Nat.is_eq(1n+ap, 0n) : Bool}, lb)
            case 1n+bp:
              pt.split_hi_eq(hp, ap, bp, la, lb)

# the empty seen tree has met no variable
def pt.st_empty_node(+h: Nat, +lo: TChase.ST, +hi: TChase.ST, +i: Nat, c: Bool, il: {TChase.st.mem(lo, i) == False{} : Bool}, ih: {TChase.st.mem(hi, Nat.sub(i, h)) == False{} : Bool}) -> {TChase.st.has(TChase.SN{h, lo, hi}, c, i) == False{} : Bool}:
  match c:
    case True{}:
      il
    case False{}:
      ih

def pt.st_empty(t: TChase.VT, +i: Nat) -> {TChase.st.mem(TChase.st.of(t), i) == False{} : Bool}:
  match t:
    case TChase.VL{xs}:
      {==}
    case TChase.VN{+h, +lo, +hi}:
      pt.st_empty_node(h, TChase.st.of(lo), TChase.st.of(hi), i, Nat.is_lt(i, h), pt.st_empty(lo, i), pt.st_empty(hi, Nat.sub(i, h)))

# a variable added is met, and every one met before stays met
def pt.st_add_node(+h: Nat, +lo: TChase.ST, +hi: TChase.ST, +k: Nat, +i: Nat, ck: Bool, ci: Bool, ek: {Nat.is_lt(k, h) == ck : Bool}, ei: {Nat.is_lt(i, h) == ci : Bool},
  il: {TChase.st.mem(TChase.st.add(lo, k), i) == Bool.or(Nat.is_eq(k, i), TChase.st.mem(lo, i)) : Bool},
  ih: {TChase.st.mem(TChase.st.add(hi, Nat.sub(k, h)), Nat.sub(i, h)) == Bool.or(Nat.is_eq(Nat.sub(k, h), Nat.sub(i, h)), TChase.st.mem(hi, Nat.sub(i, h))) : Bool})
  -> {TChase.st.has(TChase.st.ins(TChase.SN{h, lo, hi}, ck, k), ci, i) == Bool.or(Nat.is_eq(k, i), TChase.st.has(TChase.SN{h, lo, hi}, ci, i)) : Bool}:
  match ck ci:
    case True{} True{}:
      il
    case True{} False{}:
      %Equal.sym(Bool, Nat.is_eq(k, i), False{}, pt.split_lo_ne(h, k, i, ek, ei)) : {TChase.st.mem(hi, Nat.sub(i, h)) == Bool.or(_, TChase.st.mem(hi, Nat.sub(i, h))) : Bool}
      {==}
    case False{} True{}:
      %Equal.sym(Bool, Nat.is_eq(k, i), False{}, pt.split_hi_ne(h, k, i, ek, ei)) : {TChase.st.mem(lo, i) == Bool.or(_, TChase.st.mem(lo, i)) : Bool}
      {==}
    case False{} False{}:
      %pt.split_hi_eq(h, k, i, ek, ei) : {TChase.st.mem(TChase.st.add(hi, Nat.sub(k, h)), Nat.sub(i, h)) == Bool.or(_, TChase.st.mem(hi, Nat.sub(i, h))) : Bool}
      ih

# adding a variable keeps the split
def pt.ins_h(t: TChase.ST, c: Bool, +k: Nat) -> {TChase.st.h(TChase.st.ins(t, c, k)) == TChase.st.h(t) : Nat}:
  match t:
    case TChase.SL{xs}:
      {==}
    case TChase.SN{h, lo, hi}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}

def pt.st_add(t: TChase.ST, +k: Nat, +i: Nat) -> {TChase.st.mem(TChase.st.add(t, k), i) == Bool.or(Nat.is_eq(k, i), TChase.st.mem(t, i)) : Bool}:
  match t:
    case TChase.SL{+xs}:
      %Equal.sym(Bool, TChase.seen.has(xs, i, Nat.is_eq(k, i)), Bool.or(Nat.is_eq(k, i), Theme.th.mem(xs, i)), pt.has_mem(xs, i, Nat.is_eq(k, i))) : {_ == Bool.or(Nat.is_eq(k, i), TChase.seen.has(xs, i, False{})) : Bool}
      %Equal.sym(Bool, TChase.seen.has(xs, i, False{}), Bool.or(False{}, Theme.th.mem(xs, i)), pt.has_mem(xs, i, False{})) : {Bool.or(Nat.is_eq(k, i), Theme.th.mem(xs, i)) == Bool.or(Nat.is_eq(k, i), _) : Bool}
      {==}
    case TChase.SN{+h, +lo, +hi}:
      +sn = {TChase.SN{h, lo, hi} : TChase.ST}
      +ck = Nat.is_lt(k, h)
      %Equal.sym(Nat, TChase.st.h(TChase.st.ins(sn, ck, k)), TChase.st.h(sn), pt.ins_h(sn, ck, k)) : {TChase.st.has(TChase.st.ins(sn, ck, k), Nat.is_lt(i, _), i) == Bool.or(Nat.is_eq(k, i), TChase.st.mem(sn, i)) : Bool}
      pt.st_add_node(h, lo, hi, k, i, ck, Nat.is_lt(i, h), {==}, {==}, pt.st_add(lo, k, i), pt.st_add(hi, Nat.sub(k, h), Nat.sub(i, h)))

# the seen tree of t's shape with the variables xs met (the last met first)
def pt.sset(+t: TChase.VT, xs: List<&2, Nat>) -> TChase.ST:
  match xs:
    case Nil{}:
      TChase.st.of(t)
    case Con{k, rest}:
      TChase.st.add(pt.sset(t, rest), k)

# the seen tree has met exactly the variables of the list
def pt.st_sset(+t: TChase.VT, seen: List<&2, Nat>, +i: Nat) -> {TChase.st.mem(pt.sset(t, seen), i) == Theme.th.mem(seen, i) : Bool}:
  match seen:
    case Nil{}:
      pt.st_empty(t, i)
    case Con{+k, +rest}:
      +r = pt.sset(t, rest)
      %Equal.sym(Bool, TChase.st.mem(TChase.st.add(r, k), i), Bool.or(Nat.is_eq(k, i), TChase.st.mem(r, i)), pt.st_add(r, k, i)) : {_ == Bool.or(Nat.is_eq(k, i), Theme.th.mem(rest, i)) : Bool}
      %Equal.sym(Bool, TChase.st.mem(r, i), Theme.th.mem(rest, i), pt.st_sset(t, rest, i)) : {Bool.or(Nat.is_eq(k, i), _) == Bool.or(Nat.is_eq(k, i), Theme.th.mem(rest, i)) : Bool}
      {==}

# the variable tree of a file and the steps over the trees
def pt.vt(+vars: List<&2, TFile.Var>, +n: Nat) -> TChase.VT:
  TChase.vt.build(n, Nat.is_le(n, 1n), vars, n)

def pt.vt_at(+vars: List<&2, TFile.Var>, +n: Nat, +i: Nat) -> {TChase.vt.at(pt.vt(vars, n), i) == Theme.th.var(vars, i) : Maybe<&2, TFile.Json>}:
  Equal.trans(Maybe<&2, TFile.Json>, TChase.vt.at(pt.vt(vars, n), i), TChase.var.val(vars, i), Theme.th.var(vars, i), pt.vt_build(n, Nat.is_le(n, 1n), vars, n, i), pt.var_val(vars, i))

# a rule's step as a step over the trees
def pt.conv(+t: TChase.VT, s: TChase.Step) -> TChase.FStep:
  match s:
    case TChase.Stop{g}:
      TChase.FStop{g}
    case TChase.Go{seen, j}:
      TChase.FGo{pt.sset(t, seen), j}

def pt.look_next(+t: TChase.VT, m: Maybe<&2, TFile.Json>, +seen: List<&2, Nat>, s: String, +i: Nat) -> {TChase.look.next(m, TChase.st.add(pt.sset(t, seen), i), s) == pt.conv(t, Theme.th.ref(False{}, m, seen, s, i)) : TChase.FStep}:
  match m:
    case None{}:
      {==}
    case Some{j}:
      {==}

def pt.look_var(b: Bool, +vars: List<&2, TFile.Var>, +n: Nat, +seen: List<&2, Nat>, +s: String, +i: Nat) -> {TChase.look.var(b, pt.vt(vars, n), pt.sset(pt.vt(vars, n), seen), s, i) == pt.conv(pt.vt(vars, n), Theme.th.ref(b, Theme.th.var(vars, i), seen, s, i)) : TChase.FStep}:
  match b:
    case True{}:
      {==}
    case False{}:
      +V = pt.vt(vars, n)
      %Equal.sym(Maybe<&2, TFile.Json>, TChase.vt.at(V, i), Theme.th.var(vars, i), pt.vt_at(vars, n, i)) : {TChase.look.next(_, TChase.st.add(pt.sset(V, seen), i), s) == pt.conv(V, Theme.th.ref(False{}, Theme.th.var(vars, i), seen, s, i)) : TChase.FStep}
      pt.look_next(V, Theme.th.var(vars, i), seen, s, i)

def pt.look_ref(+vars: List<&2, TFile.Var>, +n: Nat, +seen: List<&2, Nat>, +s: String, at: Maybe<&2, Nat>) -> {TChase.look.ref(pt.vt(vars, n), pt.sset(pt.vt(vars, n), seen), s, at) == pt.conv(pt.vt(vars, n), Theme.th.name(vars, seen, s, at)) : TChase.FStep}:
  match at:
    case None{}:
      {==}
    case Some{+i}:
      +V = pt.vt(vars, n)
      %Equal.sym(Bool, TChase.st.mem(pt.sset(V, seen), i), Theme.th.mem(seen, i), pt.st_sset(V, seen, i)) : {TChase.look.var(_, V, pt.sset(V, seen), s, i) == pt.conv(V, Theme.th.ref(Theme.th.mem(seen, i), Theme.th.var(vars, i), seen, s, i)) : TChase.FStep}
      pt.look_var(Theme.th.mem(seen, i), vars, n, seen, s, i)

def pt.look_sym(sharp: Bool, +vars: List<&2, TFile.Var>, +n: Nat, +seen: List<&2, Nat>, +s: String, at: Maybe<&2, Nat>) -> {TChase.look.sym(sharp, pt.vt(vars, n), pt.sset(pt.vt(vars, n), seen), s, at) == pt.conv(pt.vt(vars, n), Theme.th.text.c(sharp, vars, seen, s, at)) : TChase.FStep}:
  match sharp:
    case True{}:
      Equal.cong(TChase.Got, TChase.FStep, g => TChase.FStop{g}, TChase.hex.got(Co.hex(s), s), Theme.th.hex(Co.hex(s), s), pt.hexgot(Co.hex(s), s))
    case False{}:
      pt.look_ref(vars, n, seen, s, at)

def pt.look_str(+vars: List<&2, TFile.Var>, +n: Nat, +seen: List<&2, Nat>, s: String, at: Maybe<&2, Nat>) -> {TChase.look.str(pt.vt(vars, n), pt.sset(pt.vt(vars, n), seen), s, at) == pt.conv(pt.vt(vars, n), Theme.th.text(vars, seen, s, at)) : TChase.FStep}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, rest}:
      pt.look_sym(Char.is_eq(c, '#'), vars, n, seen, SCon{c, rest}, at)

# a step over the trees is the rule's step
def pt.look_step(+vars: List<&2, TFile.Var>, +n: Nat, +seen: List<&2, Nat>, j: TFile.Json) -> {TChase.look.step(pt.vt(vars, n), pt.sset(pt.vt(vars, n), seen), j) == pt.conv(pt.vt(vars, n), Theme.th.next(vars, seen, j)) : TChase.FStep}:
  match j:
    case TFile.JStr{s, at}:
      pt.look_str(vars, n, seen, s, at)
    case TFile.JNum{+t}:
      Equal.cong(TChase.Got, TChase.FStep, g => TChase.FStop{g}, TChase.num.got(Co.num(t), t), Theme.th.num(Co.num(t), t), pt.numgot(Co.num(t), t))
    case TFile.JOther{t}:
      {==}

# the walk over the trees is the rule's walk, for any fuel
def pt.look_walk(fuel: Nat, +vars: List<&2, TFile.Var>, +n: Nat, st: TChase.Step) -> {TChase.look.walk(fuel, pt.vt(vars, n), pt.conv(pt.vt(vars, n), st)) == Theme.th.follow(fuel, vars, st) : TChase.Got}:
  match fuel:
    case 0n:
      match st:
        case TChase.Stop{g}:
          {==}
        case TChase.Go{seen, j}:
          {==}
    case 1n+f:
      match st:
        case TChase.Stop{g}:
          {==}
        case TChase.Go{+seen, +j}:
          +V = pt.vt(vars, n)
          %Equal.sym(TChase.FStep, TChase.look.step(V, pt.sset(V, seen), j), pt.conv(V, Theme.th.next(vars, seen, j)), pt.look_step(vars, n, seen, j)) : {TChase.look.walk(f, V, _) == Theme.th.follow(f, vars, Theme.th.next(vars, seen, j)) : TChase.Got}
          pt.look_walk(f, vars, n, Theme.th.next(vars, seen, j))

def Theme.theme_chase_rule(vars, j):
  pt.look_walk(1n+List.length(&2, TFile.Var, vars), vars, List.length(&2, TFile.Var, vars), TChase.Go{Nil{}, j})
