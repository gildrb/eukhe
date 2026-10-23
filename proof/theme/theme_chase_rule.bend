# eukhe: the proof of LAW theme_chase_rule

import Base
import ../../bend/color.bend as Co
import ../../bend/theme.bend as T
import ../../laws/theme.bend as Theme
import ./base.bend as LA

# Values
# ------
# The model and the rule take the same steps: the seen check of a leaf
# is the membership, the variable lookup of a leaf the list lookup.

def pt.has_mem(xs: List<&2, Nat>, +i: Nat, hit: Bool) -> {T.seen.has(xs, i, hit) == Bool.or(hit, Theme.th.mem(xs, i)) : Bool}:
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

def pt.var_val(xs: List<&2, T.Var>, n: Nat) -> {T.var.val(xs, n) == Theme.th.var(xs, n) : Maybe<&2, T.Json>}:
  match xs n:
    case Nil{} q:
      {==}
    case Con{T.Var{nm, v}, rest} 0n:
      {==}
    case Con{x, rest} 1n+p:
      pt.var_val(rest, p)

def pt.hexgot(m: Maybe<&2, Co.Rgb>, s: String) -> {T.hex.got(m, s) == Theme.th.hex(m, s) : T.Got}:
  match m:
    case None{}:
      {==}
    case Some{c}:
      {==}

def pt.numgot(m: Maybe<&2, U32>, s: String) -> {T.num.got(m, s) == Theme.th.num(m, s) : T.Got}:
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
def pt.val_take(xs: List<&2, T.Var>, +h: Nat, +i: Nat, lt: {Nat.is_lt(i, h) == True{} : Bool}) -> {T.var.val(List.take(&2, T.Var, xs, h), i) == T.var.val(xs, i) : Maybe<&2, T.Json>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case T.Var{nm, v}:
          match h:
            case 0n:
              match i:
                case 0n:
                  LA.themes.pt.absurdF({T.var.val(Nil{}, 0n) == T.var.val(T.Var{nm, v} <> rest, 0n) : Maybe<&2, T.Json>}, lt)
                case 1n+ip:
                  LA.themes.pt.absurdF({T.var.val(Nil{}, 1n+ip) == T.var.val(T.Var{nm, v} <> rest, 1n+ip) : Maybe<&2, T.Json>}, lt)
            case 1n+hp:
              match i:
                case 0n:
                  {==}
                case 1n+ip:
                  pt.val_take(rest, hp, ip, lt)

# from the split on, the variables past the first h answer as all of them
def pt.val_drop(xs: List<&2, T.Var>, +h: Nat, +i: Nat, ge: {Nat.is_lt(i, h) == False{} : Bool}) -> {T.var.val(List.drop(&2, T.Var, xs, h), Nat.sub(i, h)) == T.var.val(xs, i) : Maybe<&2, T.Json>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, rest}:
      match x:
        case T.Var{nm, v}:
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
                  LA.themes.pt.absurdT({T.var.val(List.drop(&2, T.Var, T.Var{nm, v} <> rest, 1n+hp), Nat.sub(0n, 1n+hp)) == T.var.val(T.Var{nm, v} <> rest, 0n) : Maybe<&2, T.Json>}, ge)
                case 1n+ip:
                  pt.val_drop(rest, hp, ip, ge)

def pt.vt_node(+h: Nat, +a: T.VT, +b: T.VT, +xs: List<&2, T.Var>, +i: Nat, c: Bool, e: {Nat.is_lt(i, h) == c : Bool},
  ia: {T.vt.at(a, i) == T.var.val(List.take(&2, T.Var, xs, h), i) : Maybe<&2, T.Json>},
  ib: {T.vt.at(b, Nat.sub(i, h)) == T.var.val(List.drop(&2, T.Var, xs, h), Nat.sub(i, h)) : Maybe<&2, T.Json>})
  -> {T.vt.get(T.VN{h, a, b}, c, i) == T.var.val(xs, i) : Maybe<&2, T.Json>}:
  match c:
    case True{}:
      Equal.trans(Maybe<&2, T.Json>, T.vt.at(a, i), T.var.val(List.take(&2, T.Var, xs, h), i), T.var.val(xs, i), ia, pt.val_take(xs, h, i, e))
    case False{}:
      Equal.trans(Maybe<&2, T.Json>, T.vt.at(b, Nat.sub(i, h)), T.var.val(List.drop(&2, T.Var, xs, h), Nat.sub(i, h)), T.var.val(xs, i), ib, pt.val_drop(xs, h, i, e))

# the tree of the variables answers as their list, whatever its splits
def pt.vt_build(fuel: Nat, small: Bool, +xs: List<&2, T.Var>, +n: Nat, +i: Nat) -> {T.vt.at(T.vt.build(fuel, small, xs, n), i) == T.var.val(xs, i) : Maybe<&2, T.Json>}:
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
          +ta = List.take(&2, T.Var, xs, h)
          +tb = List.drop(&2, T.Var, xs, h)
          +a = T.vt.build(f, Nat.is_le(h, 1n), ta, h)
          +b = T.vt.build(f, Nat.is_le(r, 1n), tb, r)
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
def pt.st_empty_node(+h: Nat, +lo: T.ST, +hi: T.ST, +i: Nat, c: Bool, il: {T.st.mem(lo, i) == False{} : Bool}, ih: {T.st.mem(hi, Nat.sub(i, h)) == False{} : Bool}) -> {T.st.has(T.SN{h, lo, hi}, c, i) == False{} : Bool}:
  match c:
    case True{}:
      il
    case False{}:
      ih

def pt.st_empty(t: T.VT, +i: Nat) -> {T.st.mem(T.st.of(t), i) == False{} : Bool}:
  match t:
    case T.VL{xs}:
      {==}
    case T.VN{+h, +lo, +hi}:
      pt.st_empty_node(h, T.st.of(lo), T.st.of(hi), i, Nat.is_lt(i, h), pt.st_empty(lo, i), pt.st_empty(hi, Nat.sub(i, h)))

# a variable added is met, and every one met before stays met
def pt.st_add_node(+h: Nat, +lo: T.ST, +hi: T.ST, +k: Nat, +i: Nat, ck: Bool, ci: Bool, ek: {Nat.is_lt(k, h) == ck : Bool}, ei: {Nat.is_lt(i, h) == ci : Bool},
  il: {T.st.mem(T.st.add(lo, k), i) == Bool.or(Nat.is_eq(k, i), T.st.mem(lo, i)) : Bool},
  ih: {T.st.mem(T.st.add(hi, Nat.sub(k, h)), Nat.sub(i, h)) == Bool.or(Nat.is_eq(Nat.sub(k, h), Nat.sub(i, h)), T.st.mem(hi, Nat.sub(i, h))) : Bool})
  -> {T.st.has(T.st.ins(T.SN{h, lo, hi}, ck, k), ci, i) == Bool.or(Nat.is_eq(k, i), T.st.has(T.SN{h, lo, hi}, ci, i)) : Bool}:
  match ck ci:
    case True{} True{}:
      il
    case True{} False{}:
      %Equal.sym(Bool, Nat.is_eq(k, i), False{}, pt.split_lo_ne(h, k, i, ek, ei)) : {T.st.mem(hi, Nat.sub(i, h)) == Bool.or(_, T.st.mem(hi, Nat.sub(i, h))) : Bool}
      {==}
    case False{} True{}:
      %Equal.sym(Bool, Nat.is_eq(k, i), False{}, pt.split_hi_ne(h, k, i, ek, ei)) : {T.st.mem(lo, i) == Bool.or(_, T.st.mem(lo, i)) : Bool}
      {==}
    case False{} False{}:
      %pt.split_hi_eq(h, k, i, ek, ei) : {T.st.mem(T.st.add(hi, Nat.sub(k, h)), Nat.sub(i, h)) == Bool.or(_, T.st.mem(hi, Nat.sub(i, h))) : Bool}
      ih

# adding a variable keeps the split
def pt.ins_h(t: T.ST, c: Bool, +k: Nat) -> {T.st.h(T.st.ins(t, c, k)) == T.st.h(t) : Nat}:
  match t:
    case T.SL{xs}:
      {==}
    case T.SN{h, lo, hi}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}

def pt.st_add(t: T.ST, +k: Nat, +i: Nat) -> {T.st.mem(T.st.add(t, k), i) == Bool.or(Nat.is_eq(k, i), T.st.mem(t, i)) : Bool}:
  match t:
    case T.SL{+xs}:
      %Equal.sym(Bool, T.seen.has(xs, i, Nat.is_eq(k, i)), Bool.or(Nat.is_eq(k, i), Theme.th.mem(xs, i)), pt.has_mem(xs, i, Nat.is_eq(k, i))) : {_ == Bool.or(Nat.is_eq(k, i), T.seen.has(xs, i, False{})) : Bool}
      %Equal.sym(Bool, T.seen.has(xs, i, False{}), Bool.or(False{}, Theme.th.mem(xs, i)), pt.has_mem(xs, i, False{})) : {Bool.or(Nat.is_eq(k, i), Theme.th.mem(xs, i)) == Bool.or(Nat.is_eq(k, i), _) : Bool}
      {==}
    case T.SN{+h, +lo, +hi}:
      +sn = {T.SN{h, lo, hi} : T.ST}
      +ck = Nat.is_lt(k, h)
      %Equal.sym(Nat, T.st.h(T.st.ins(sn, ck, k)), T.st.h(sn), pt.ins_h(sn, ck, k)) : {T.st.has(T.st.ins(sn, ck, k), Nat.is_lt(i, _), i) == Bool.or(Nat.is_eq(k, i), T.st.mem(sn, i)) : Bool}
      pt.st_add_node(h, lo, hi, k, i, ck, Nat.is_lt(i, h), {==}, {==}, pt.st_add(lo, k, i), pt.st_add(hi, Nat.sub(k, h), Nat.sub(i, h)))

# the seen tree of t's shape with the variables xs met (the last met first)
def pt.sset(+t: T.VT, xs: List<&2, Nat>) -> T.ST:
  match xs:
    case Nil{}:
      T.st.of(t)
    case Con{k, rest}:
      T.st.add(pt.sset(t, rest), k)

# the seen tree has met exactly the variables of the list
def pt.st_sset(+t: T.VT, seen: List<&2, Nat>, +i: Nat) -> {T.st.mem(pt.sset(t, seen), i) == Theme.th.mem(seen, i) : Bool}:
  match seen:
    case Nil{}:
      pt.st_empty(t, i)
    case Con{+k, +rest}:
      +r = pt.sset(t, rest)
      %Equal.sym(Bool, T.st.mem(T.st.add(r, k), i), Bool.or(Nat.is_eq(k, i), T.st.mem(r, i)), pt.st_add(r, k, i)) : {_ == Bool.or(Nat.is_eq(k, i), Theme.th.mem(rest, i)) : Bool}
      %Equal.sym(Bool, T.st.mem(r, i), Theme.th.mem(rest, i), pt.st_sset(t, rest, i)) : {Bool.or(Nat.is_eq(k, i), _) == Bool.or(Nat.is_eq(k, i), Theme.th.mem(rest, i)) : Bool}
      {==}

# the variable tree of a file and the steps over the trees
def pt.vt(+vars: List<&2, T.Var>, +n: Nat) -> T.VT:
  T.vt.build(n, Nat.is_le(n, 1n), vars, n)

def pt.vt_at(+vars: List<&2, T.Var>, +n: Nat, +i: Nat) -> {T.vt.at(pt.vt(vars, n), i) == Theme.th.var(vars, i) : Maybe<&2, T.Json>}:
  Equal.trans(Maybe<&2, T.Json>, T.vt.at(pt.vt(vars, n), i), T.var.val(vars, i), Theme.th.var(vars, i), pt.vt_build(n, Nat.is_le(n, 1n), vars, n, i), pt.var_val(vars, i))

# a rule's step as a step over the trees
def pt.conv(+t: T.VT, s: T.Step) -> T.FStep:
  match s:
    case T.Stop{g}:
      T.FStop{g}
    case T.Go{seen, j}:
      T.FGo{pt.sset(t, seen), j}

def pt.look_next(+t: T.VT, m: Maybe<&2, T.Json>, +seen: List<&2, Nat>, s: String, +i: Nat) -> {T.look.next(m, T.st.add(pt.sset(t, seen), i), s) == pt.conv(t, Theme.th.ref(False{}, m, seen, s, i)) : T.FStep}:
  match m:
    case None{}:
      {==}
    case Some{j}:
      {==}

def pt.look_var(b: Bool, +vars: List<&2, T.Var>, +n: Nat, +seen: List<&2, Nat>, +s: String, +i: Nat) -> {T.look.var(b, pt.vt(vars, n), pt.sset(pt.vt(vars, n), seen), s, i) == pt.conv(pt.vt(vars, n), Theme.th.ref(b, Theme.th.var(vars, i), seen, s, i)) : T.FStep}:
  match b:
    case True{}:
      {==}
    case False{}:
      +V = pt.vt(vars, n)
      %Equal.sym(Maybe<&2, T.Json>, T.vt.at(V, i), Theme.th.var(vars, i), pt.vt_at(vars, n, i)) : {T.look.next(_, T.st.add(pt.sset(V, seen), i), s) == pt.conv(V, Theme.th.ref(False{}, Theme.th.var(vars, i), seen, s, i)) : T.FStep}
      pt.look_next(V, Theme.th.var(vars, i), seen, s, i)

def pt.look_ref(+vars: List<&2, T.Var>, +n: Nat, +seen: List<&2, Nat>, +s: String, at: Maybe<&2, Nat>) -> {T.look.ref(pt.vt(vars, n), pt.sset(pt.vt(vars, n), seen), s, at) == pt.conv(pt.vt(vars, n), Theme.th.name(vars, seen, s, at)) : T.FStep}:
  match at:
    case None{}:
      {==}
    case Some{+i}:
      +V = pt.vt(vars, n)
      %Equal.sym(Bool, T.st.mem(pt.sset(V, seen), i), Theme.th.mem(seen, i), pt.st_sset(V, seen, i)) : {T.look.var(_, V, pt.sset(V, seen), s, i) == pt.conv(V, Theme.th.ref(Theme.th.mem(seen, i), Theme.th.var(vars, i), seen, s, i)) : T.FStep}
      pt.look_var(Theme.th.mem(seen, i), vars, n, seen, s, i)

def pt.look_sym(sharp: Bool, +vars: List<&2, T.Var>, +n: Nat, +seen: List<&2, Nat>, +s: String, at: Maybe<&2, Nat>) -> {T.look.sym(sharp, pt.vt(vars, n), pt.sset(pt.vt(vars, n), seen), s, at) == pt.conv(pt.vt(vars, n), Theme.th.text.c(sharp, vars, seen, s, at)) : T.FStep}:
  match sharp:
    case True{}:
      Equal.cong(T.Got, T.FStep, g => T.FStop{g}, T.hex.got(Co.hex(s), s), Theme.th.hex(Co.hex(s), s), pt.hexgot(Co.hex(s), s))
    case False{}:
      pt.look_ref(vars, n, seen, s, at)

def pt.look_str(+vars: List<&2, T.Var>, +n: Nat, +seen: List<&2, Nat>, s: String, at: Maybe<&2, Nat>) -> {T.look.str(pt.vt(vars, n), pt.sset(pt.vt(vars, n), seen), s, at) == pt.conv(pt.vt(vars, n), Theme.th.text(vars, seen, s, at)) : T.FStep}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, rest}:
      pt.look_sym(Char.is_eq(c, '#'), vars, n, seen, SCon{c, rest}, at)

# a step over the trees is the rule's step
def pt.look_step(+vars: List<&2, T.Var>, +n: Nat, +seen: List<&2, Nat>, j: T.Json) -> {T.look.step(pt.vt(vars, n), pt.sset(pt.vt(vars, n), seen), j) == pt.conv(pt.vt(vars, n), Theme.th.next(vars, seen, j)) : T.FStep}:
  match j:
    case T.JStr{s, at}:
      pt.look_str(vars, n, seen, s, at)
    case T.JNum{+t}:
      Equal.cong(T.Got, T.FStep, g => T.FStop{g}, T.num.got(Co.num(t), t), Theme.th.num(Co.num(t), t), pt.numgot(Co.num(t), t))
    case T.JOther{t}:
      {==}

# the walk over the trees is the rule's walk, for any fuel
def pt.look_walk(fuel: Nat, +vars: List<&2, T.Var>, +n: Nat, st: T.Step) -> {T.look.walk(fuel, pt.vt(vars, n), pt.conv(pt.vt(vars, n), st)) == Theme.th.follow(fuel, vars, st) : T.Got}:
  match fuel:
    case 0n:
      match st:
        case T.Stop{g}:
          {==}
        case T.Go{seen, j}:
          {==}
    case 1n+f:
      match st:
        case T.Stop{g}:
          {==}
        case T.Go{+seen, +j}:
          +V = pt.vt(vars, n)
          %Equal.sym(T.FStep, T.look.step(V, pt.sset(V, seen), j), pt.conv(V, Theme.th.next(vars, seen, j)), pt.look_step(vars, n, seen, j)) : {T.look.walk(f, V, _) == Theme.th.follow(f, vars, Theme.th.next(vars, seen, j)) : T.Got}
          pt.look_walk(f, vars, n, Theme.th.next(vars, seen, j))

def Theme.theme_chase_rule(vars, j):
  pt.look_walk(1n+List.length(&2, T.Var, vars), vars, List.length(&2, T.Var, vars), T.Go{Nil{}, j})
