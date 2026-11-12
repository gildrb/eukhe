# eukhe: the proof of LAW theme_pick_clashes_first
# The clashes of a pick are the model's clashes over all the files. The
# search for the first file named m answers w exactly when the file at w
# is named m and none before it is (cf.first); a file reports a clash, at
# its own index, with the first file of its name when that is another file
# (cf.at); so over the files from index at (the files past at - 1), the
# clashes at at + i are those of the file at at + i (cf.mem), none is
# below at (cf.below), and they rise (cf.rising).

import Base
import ../../bend/theme/choice.bend as TChoice
import ../../bend/theme/name.bend as TName
import ../../laws/theme_pick.bend as ThemePick
import ./base.bend as LA
import ../theme/base.bend as LT
import ./theme_pick_broken_once.bend as BO

# Lists
# -----

def cf.LI(xs: List<&2, TChoice.Ld>, G: Type) -> Type:
  match xs:
    case Nil{}:
      Unit
    case Con{x, t}:
      G

def cf.nil_con(-x: TChoice.Ld, -t: List<&2, TChoice.Ld>, -G: Type, e: {Nil{} == x <> t : List<&2, TChoice.Ld>}) -> G:
  %e : cf.LI(_, G)
  Unit{}

def cf.hd(xs: List<&2, TChoice.Ld>) -> Maybe<&2, TChoice.Ld>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, t}:
      Some{x}

def cf.tl(xs: List<&2, TChoice.Ld>) -> List<&2, TChoice.Ld>:
  match xs:
    case Nil{}:
      Nil{}
    case Con{x, t}:
      t

def cf.drop0(xs: List<&2, TChoice.Ld>) -> {List.drop(&2, TChoice.Ld, xs, 0n) == xs : List<&2, TChoice.Ld>}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, t}:
      {==}

# the files from at are l, then rest: the file at at is l
def cf.dget(all: List<&2, TChoice.Ld>, at: Nat, -l: TChoice.Ld, -rest: List<&2, TChoice.Ld>, h: {List.drop(&2, TChoice.Ld, all, at) == l <> rest : List<&2, TChoice.Ld>}) -> {List.get(&2, TChoice.Ld, all, at) == Some{l} : Maybe<&2, TChoice.Ld>}:
  match all at:
    case Nil{} q:
      cf.nil_con(l, rest, {List.get(&2, TChoice.Ld, Nil{}, q) == Some{l} : Maybe<&2, TChoice.Ld>}, h)
    case Con{x, t} 0n:
      Equal.cong(List<&2, TChoice.Ld>, Maybe<&2, TChoice.Ld>, ys => cf.hd(ys), x <> t, l <> rest, h)
    case Con{x, t} 1n+p:
      cf.dget(t, p, l, rest, h)

# the files from at are l, then rest: the files from at + 1 are rest
def cf.dnext(all: List<&2, TChoice.Ld>, at: Nat, -l: TChoice.Ld, -rest: List<&2, TChoice.Ld>, h: {List.drop(&2, TChoice.Ld, all, at) == l <> rest : List<&2, TChoice.Ld>}) -> {List.drop(&2, TChoice.Ld, all, 1n+at) == rest : List<&2, TChoice.Ld>}:
  match all at:
    case Nil{} q:
      cf.nil_con(l, rest, {List.drop(&2, TChoice.Ld, Nil{}, 1n+q) == rest : List<&2, TChoice.Ld>}, h)
    case Con{x, +t} 0n:
      Equal.trans(List<&2, TChoice.Ld>, List.drop(&2, TChoice.Ld, t, 0n), t, rest, cf.drop0(t), Equal.cong(List<&2, TChoice.Ld>, List<&2, TChoice.Ld>, ys => cf.tl(ys), x <> t, l <> rest, h))
    case Con{x, t} 1n+p:
      cf.dnext(t, p, l, rest, h)

# no file from at: nothing at at + i
def cf.dnone(all: List<&2, TChoice.Ld>, at: Nat, -i: Nat, h: {List.drop(&2, TChoice.Ld, all, at) == Nil{} : List<&2, TChoice.Ld>}) -> {List.get(&2, TChoice.Ld, all, Nat.add(at, i)) == None{} : Maybe<&2, TChoice.Ld>}:
  match all at:
    case Nil{} q:
      {==}
    case Con{x, t} 0n:
      cf.nil_con(x, t, {List.get(&2, TChoice.Ld, x <> t, Nat.add(0n, i)) == None{} : Maybe<&2, TChoice.Ld>}, Equal.sym(List<&2, TChoice.Ld>, x <> t, Nil{}, h))
    case Con{x, t} 1n+p:
      cf.dnone(t, p, i, h)

def cf.eq(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      LT.themes.pt.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      LT.themes.pt.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, cf.eq(p, q, h))

# Bools
# -----

def cf.and_f(x: Bool) -> {Bool.and(x, False{}) == False{} : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

def cf.or_f(x: Bool) -> {Bool.or(x, False{}) == x : Bool}:
  match x:
    case True{}:
      {==}
    case False{}:
      {==}

# The first file of a name
# ------------------------

def cf.is(m: Maybe<&2, Nat>, +w: Nat) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      Nat.is_eq(x, w)

def cf.fbelow_pick(b: Bool, +a: Nat, -f: Maybe<&2, Nat>, +j: Nat, lt: {Nat.is_lt(j, a) == True{} : Bool}, ih: {cf.is(f, j) == False{} : Bool}) -> {cf.is(TChoice.first.pick(b, a, f), j) == False{} : Bool}:
  match b:
    case True{}:
      BO.bo.lt_ne(j, a, lt)
    case False{}:
      ih

# the search from index a finds nothing below a
def cf.fbelow(ls: List<&2, TChoice.Ld>, +m: String, +a: Nat, +j: Nat, +lt: {Nat.is_lt(j, a) == True{} : Bool}) -> {cf.is(TChoice.fine.first(ls, m, a), j) == False{} : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{l, +rest}:
      cf.fbelow_pick(TChoice.fine.named(l, m), a, TChoice.fine.first(rest, m, 1n+a), j, lt, cf.fbelow(rest, m, 1n+a, j, BO.bo.lt_succ(j, a, lt)))

def cf.fhere_b(b: Bool, +a: Nat, -f: Maybe<&2, Nat>, -u: Bool, hf: {cf.is(f, a) == False{} : Bool}) -> {cf.is(TChoice.first.pick(b, a, f), a) == Bool.and(b, True{}) : Bool}:
  match b:
    case True{}:
      BO.bo.eq_refl(a)
    case False{}:
      hf

def cf.fhere(l: TChoice.Ld, +m: String, +a: Nat, -f: Maybe<&2, Nat>, hf: {cf.is(f, a) == False{} : Bool}) -> {cf.is(TChoice.first.pick(TChoice.fine.named(l, m), a, f), a) == Bool.and(ThemePick.th.same(ThemePick.th.name.of(Some{l}), m), True{}) : Bool}:
  match l:
    case TChoice.Fine{nm, c}:
      cf.fhere_b(String.eq(nm, m), a, f, True{}, hf)
    case TChoice.Broke{nm, st}:
      hf

def cf.fthere_b(b: Bool, +a: Nat, -f: Maybe<&2, Nat>, +j: Nat, +s: Bool, -u: Bool, hne: {Nat.is_eq(a, j) == False{} : Bool}, ih: {cf.is(f, j) == Bool.and(s, u) : Bool}) -> {cf.is(TChoice.first.pick(b, a, f), j) == Bool.and(s, Bool.and(Bool.not(b), u)) : Bool}:
  match b:
    case True{}:
      %Equal.sym(Bool, Bool.and(s, False{}), False{}, cf.and_f(s)) : {cf.is(Some{a}, j) == _ : Bool}
      hne
    case False{}:
      ih

def cf.fthere(l: TChoice.Ld, +m: String, +a: Nat, -f: Maybe<&2, Nat>, +j: Nat, +s: Bool, -xs: List<&2, TChoice.Ld>, hne: {Nat.is_eq(a, j) == False{} : Bool}, ih: {cf.is(f, j) == Bool.and(s, ThemePick.th.unnamed(xs, m)) : Bool}) -> {cf.is(TChoice.first.pick(TChoice.fine.named(l, m), a, f), j) == Bool.and(s, ThemePick.th.unnamed(l <> xs, m)) : Bool}:
  match l:
    case TChoice.Fine{nm, c}:
      cf.fthere_b(String.eq(nm, m), a, f, j, s, ThemePick.th.unnamed(xs, m), hne, ih)
    case TChoice.Broke{nm, st}:
      ih

# the search for the first file named m answers w exactly when the file at
# w is named m and no file before it is
def cf.first(ls: List<&2, TChoice.Ld>, +m: String, +a: Nat, w: Nat) -> {cf.is(TChoice.fine.first(ls, m, a), Nat.add(a, w)) == Bool.and(ThemePick.th.same(ThemePick.th.name.at(ls, w), m), ThemePick.th.unnamed(List.take(&2, TChoice.Ld, ls, w), m)) : Bool}:
  match ls w:
    case Nil{} q:
      {==}
    case Con{+l, +rest} 0n:
      %LA.pk.add0(a) : {cf.is(TChoice.first.pick(TChoice.fine.named(l, m), a, TChoice.fine.first(rest, m, 1n+a)), _) == Bool.and(ThemePick.th.same(ThemePick.th.name.of(Some{l}), m), True{}) : Bool}
      cf.fhere(l, m, a, TChoice.fine.first(rest, m, 1n+a), cf.fbelow(rest, m, 1n+a, a, BO.bo.lt_self(a)))
    case Con{+l, +rest} 1n++p:
      %Equal.sym(Nat, Nat.add(a, 1n+p), 1n+Nat.add(a, p), LA.pk.add_succ(a, p)) : {cf.is(TChoice.first.pick(TChoice.fine.named(l, m), a, TChoice.fine.first(rest, m, 1n+a)), _) == Bool.and(ThemePick.th.same(ThemePick.th.name.at(rest, p), m), ThemePick.th.unnamed(l <> List.take(&2, TChoice.Ld, rest, p), m)) : Bool}
      cf.fthere(l, m, a, TChoice.fine.first(rest, m, 1n+a), 1n+Nat.add(a, p), ThemePick.th.same(ThemePick.th.name.at(rest, p), m), List.take(&2, TChoice.Ld, rest, p), BO.bo.ne_succ(a, p), cf.first(rest, m, 1n+a, p))

# A file's clash
# --------------
# The clash a file reports, at its own index at: with the first file of
# its name, when that is another file.

def cf.wif(e: Bool, w0: Nat) -> Maybe<&2, Nat>:
  match e:
    case True{}:
      None{}
    case False{}:
      Some{w0}

def cf.wf(f: Maybe<&2, Nat>, +at: Nat) -> Maybe<&2, Nat>:
  match f:
    case None{}:
      None{}
    case Some{+w0}:
      cf.wif(Nat.is_eq(w0, at), w0)

def cf.w(+all: List<&2, TChoice.Ld>, l: TChoice.Ld, +at: Nat) -> Maybe<&2, Nat>:
  match l:
    case TChoice.Fine{+m, c}:
      cf.wf(TChoice.fine.first(all, m, 0n), at)
    case TChoice.Broke{nm, st}:
      None{}

def cf.mk(at: Nat, mw: Maybe<&2, Nat>) -> Maybe<&2, TChoice.Clash>:
  match mw:
    case None{}:
      None{}
    case Some{w0}:
      Some{TChoice.Clash{at, w0}}

def cf.ca_e(e: Bool, +w0: Nat, +at: Nat) -> {TChoice.clash.if(e, w0, at) == cf.mk(at, cf.wif(e, w0)) : Maybe<&2, TChoice.Clash>}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def cf.ca_f(f: Maybe<&2, Nat>, +at: Nat) -> {TChoice.clash.of(f, at) == cf.mk(at, cf.wf(f, at)) : Maybe<&2, TChoice.Clash>}:
  match f:
    case None{}:
      {==}
    case Some{+w0}:
      cf.ca_e(Nat.is_eq(w0, at), w0, at)

def cf.ca(+all: List<&2, TChoice.Ld>, l: TChoice.Ld, +at: Nat) -> {TChoice.clash.at(all, l, at) == cf.mk(at, cf.w(all, l, at)) : Maybe<&2, TChoice.Clash>}:
  match l:
    case TChoice.Fine{+m, c}:
      cf.ca_f(TChoice.fine.first(all, m, 0n), at)
    case TChoice.Broke{nm, st}:
      {==}

# Membership
# ----------

# a clash of the file at at is no clash at j (another index)
def cf.there(mw: Maybe<&2, Nat>, +at: Nat, -r: List<&2, TChoice.Clash>, +j: Nat, +w: Nat, -x: Bool, hne: {Nat.is_eq(at, j) == False{} : Bool}, ih: {ThemePick.th.clash.in(r, j, w) == x : Bool}) -> {ThemePick.th.clash.in(TChoice.clash.cons(cf.mk(at, mw), r), j, w) == x : Bool}:
  match mw:
    case None{}:
      ih
    case Some{w0}:
      %Equal.sym(Bool, Nat.is_eq(at, j), False{}, hne) : {Bool.or(Bool.and(_, Nat.is_eq(w0, w)), ThemePick.th.clash.in(r, j, w)) == x : Bool}
      ih

# the clashes from at report no file below at
def cf.below(+all: List<&2, TChoice.Ld>, sub: List<&2, TChoice.Ld>, +at: Nat, +j: Nat, +w: Nat, +lt: {Nat.is_lt(j, at) == True{} : Bool}) -> {ThemePick.th.clash.in(TChoice.clashes.go(all, sub, at), j, w) == False{} : Bool}:
  match sub:
    case Nil{}:
      {==}
    case Con{+l, +rest}:
      %Equal.sym(Maybe<&2, TChoice.Clash>, TChoice.clash.at(all, l, at), cf.mk(at, cf.w(all, l, at)), cf.ca(all, l, at)) : {ThemePick.th.clash.in(TChoice.clash.cons(_, TChoice.clashes.go(all, rest, 1n+at)), j, w) == False{} : Bool}
      cf.there(cf.w(all, l, at), at, TChoice.clashes.go(all, rest, 1n+at), j, w, False{}, BO.bo.lt_ne(j, at, lt), cf.below(all, rest, 1n+at, j, w, BO.bo.lt_succ(j, at, lt)))

# the clash of the file at at, at at: by the first file of its name
def cf.here_e(e1: Bool, e2: Bool, +w0: Nat, +at: Nat, -r: List<&2, TChoice.Clash>, +w: Nat, he1: {Nat.is_eq(w0, at) == e1 : Bool}, +he2: {Nat.is_eq(w0, w) == e2 : Bool}, hb: {ThemePick.th.clash.in(r, at, w) == False{} : Bool})
  -> {ThemePick.th.clash.in(TChoice.clash.cons(cf.mk(at, cf.wif(e1, w0)), r), at, w) == Bool.and(Bool.not(Nat.is_eq(w, at)), e2) : Bool}:
  match e1 e2:
    case True{} True{}:
      %cf.eq(w0, w, he2) : {ThemePick.th.clash.in(r, at, w) == Bool.and(Bool.not(Nat.is_eq(_, at)), True{}) : Bool}
      %Equal.sym(Bool, Nat.is_eq(w0, at), True{}, he1) : {ThemePick.th.clash.in(r, at, w) == Bool.and(Bool.not(_), True{}) : Bool}
      hb
    case True{} False{}:
      %Equal.sym(Bool, Bool.and(Bool.not(Nat.is_eq(w, at)), False{}), False{}, cf.and_f(Bool.not(Nat.is_eq(w, at)))) : {ThemePick.th.clash.in(r, at, w) == _ : Bool}
      hb
    case False{} True{}:
      %cf.eq(w0, w, he2) : {Bool.or(Bool.and(Nat.is_eq(at, at), Nat.is_eq(w0, w)), ThemePick.th.clash.in(r, at, w)) == Bool.and(Bool.not(Nat.is_eq(_, at)), True{}) : Bool}
      %Equal.sym(Bool, Nat.is_eq(w0, at), False{}, he1) : {Bool.or(Bool.and(Nat.is_eq(at, at), Nat.is_eq(w0, w)), ThemePick.th.clash.in(r, at, w)) == Bool.and(Bool.not(_), True{}) : Bool}
      %Equal.sym(Bool, Nat.is_eq(at, at), True{}, BO.bo.eq_refl(at)) : {Bool.or(Bool.and(_, Nat.is_eq(w0, w)), ThemePick.th.clash.in(r, at, w)) == True{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(w0, w), True{}, he2) : {Bool.or(_, ThemePick.th.clash.in(r, at, w)) == True{} : Bool}
      {==}
    case False{} False{}:
      %Equal.sym(Bool, Bool.and(Bool.not(Nat.is_eq(w, at)), False{}), False{}, cf.and_f(Bool.not(Nat.is_eq(w, at)))) : {Bool.or(Bool.and(Nat.is_eq(at, at), Nat.is_eq(w0, w)), ThemePick.th.clash.in(r, at, w)) == _ : Bool}
      %Equal.sym(Bool, Nat.is_eq(at, at), True{}, BO.bo.eq_refl(at)) : {Bool.or(Bool.and(_, Nat.is_eq(w0, w)), ThemePick.th.clash.in(r, at, w)) == False{} : Bool}
      %Equal.sym(Bool, Nat.is_eq(w0, w), False{}, he2) : {Bool.or(_, ThemePick.th.clash.in(r, at, w)) == False{} : Bool}
      hb

def cf.here_f(f: Maybe<&2, Nat>, +at: Nat, -r: List<&2, TChoice.Clash>, +w: Nat, hb: {ThemePick.th.clash.in(r, at, w) == False{} : Bool})
  -> {ThemePick.th.clash.in(TChoice.clash.cons(cf.mk(at, cf.wf(f, at)), r), at, w) == Bool.and(Bool.not(Nat.is_eq(w, at)), cf.is(f, w)) : Bool}:
  match f:
    case None{}:
      %Equal.sym(Bool, Bool.and(Bool.not(Nat.is_eq(w, at)), False{}), False{}, cf.and_f(Bool.not(Nat.is_eq(w, at)))) : {ThemePick.th.clash.in(r, at, w) == _ : Bool}
      hb
    case Some{+w0}:
      cf.here_e(Nat.is_eq(w0, at), Nat.is_eq(w0, w), w0, at, r, w, {==}, {==}, hb)

def cf.here(l: TChoice.Ld, +all: List<&2, TChoice.Ld>, +at: Nat, -r: List<&2, TChoice.Clash>, +w: Nat, hb: {ThemePick.th.clash.in(r, at, w) == False{} : Bool})
  -> {ThemePick.th.clash.in(TChoice.clash.cons(cf.mk(at, cf.w(all, l, at)), r), at, w) == ThemePick.th.clash.name(ThemePick.th.name.of(Some{l}), all, at, w) : Bool}:
  match l:
    case TChoice.Fine{+m, c}:
      %cf.first(all, m, 0n, w) : {ThemePick.th.clash.in(TChoice.clash.cons(cf.mk(at, cf.wf(TChoice.fine.first(all, m, 0n), at)), r), at, w) == Bool.and(Bool.not(Nat.is_eq(w, at)), _) : Bool}
      cf.here_f(TChoice.fine.first(all, m, 0n), at, r, w, hb)
    case TChoice.Broke{nm, st}:
      hb

# the clashes from at report, at at + i, the clash of the file there
def cf.mem(+all: List<&2, TChoice.Ld>, sub: List<&2, TChoice.Ld>, +at: Nat, i: Nat, +w: Nat, hd: {List.drop(&2, TChoice.Ld, all, at) == sub : List<&2, TChoice.Ld>})
  -> {ThemePick.th.clash.in(TChoice.clashes.go(all, sub, at), Nat.add(at, i), w) == ThemePick.th.clash.ok(all, Nat.add(at, i), w) : Bool}:
  match sub i:
    case Nil{} q:
      %Equal.sym(Maybe<&2, TChoice.Ld>, List.get(&2, TChoice.Ld, all, Nat.add(at, q)), None{}, cf.dnone(all, at, q, hd)) : {False{} == ThemePick.th.clash.name(ThemePick.th.name.of(_), all, Nat.add(at, q), w) : Bool}
      {==}
    case Con{+l, +rest} 0n:
      %LA.pk.add0(at) : {ThemePick.th.clash.in(TChoice.clashes.go(all, l <> rest, at), _, w) == ThemePick.th.clash.ok(all, _, w) : Bool}
      %Equal.sym(Maybe<&2, TChoice.Ld>, List.get(&2, TChoice.Ld, all, at), Some{l}, cf.dget(all, at, l, rest, hd)) : {ThemePick.th.clash.in(TChoice.clashes.go(all, l <> rest, at), at, w) == ThemePick.th.clash.name(ThemePick.th.name.of(_), all, at, w) : Bool}
      %Equal.sym(Maybe<&2, TChoice.Clash>, TChoice.clash.at(all, l, at), cf.mk(at, cf.w(all, l, at)), cf.ca(all, l, at)) : {ThemePick.th.clash.in(TChoice.clash.cons(_, TChoice.clashes.go(all, rest, 1n+at)), at, w) == ThemePick.th.clash.name(ThemePick.th.name.of(Some{l}), all, at, w) : Bool}
      cf.here(l, all, at, TChoice.clashes.go(all, rest, 1n+at), w, cf.below(all, rest, 1n+at, at, w, BO.bo.lt_self(at)))
    case Con{+l, +rest} 1n++p:
      %Equal.sym(Nat, Nat.add(at, 1n+p), 1n+Nat.add(at, p), LA.pk.add_succ(at, p)) : {ThemePick.th.clash.in(TChoice.clashes.go(all, l <> rest, at), _, w) == ThemePick.th.clash.ok(all, _, w) : Bool}
      %Equal.sym(Maybe<&2, TChoice.Clash>, TChoice.clash.at(all, l, at), cf.mk(at, cf.w(all, l, at)), cf.ca(all, l, at)) : {ThemePick.th.clash.in(TChoice.clash.cons(_, TChoice.clashes.go(all, rest, 1n+at)), 1n+Nat.add(at, p), w) == ThemePick.th.clash.ok(all, 1n+Nat.add(at, p), w) : Bool}
      cf.there(cf.w(all, l, at), at, TChoice.clashes.go(all, rest, 1n+at), 1n+Nat.add(at, p), w, ThemePick.th.clash.ok(all, 1n+Nat.add(at, p), w), BO.bo.ne_succ(at, p), cf.mem(all, rest, 1n+at, p, w, cf.dnext(all, at, l, rest, hd)))

# Order
# -----

def cf.above_m(mw: Maybe<&2, Nat>, +a: Nat, -r: List<&2, TChoice.Clash>, +x: Nat, lt: {Nat.is_lt(x, a) == True{} : Bool}, ih: {ThemePick.th.clash.above(r, x) == True{} : Bool}) -> {ThemePick.th.clash.above(TChoice.clash.cons(cf.mk(a, mw), r), x) == True{} : Bool}:
  match mw:
    case None{}:
      ih
    case Some{w0}:
      lt

def cf.above(+all: List<&2, TChoice.Ld>, sub: List<&2, TChoice.Ld>, +a: Nat, +x: Nat, +lt: {Nat.is_lt(x, a) == True{} : Bool}) -> {ThemePick.th.clash.above(TChoice.clashes.go(all, sub, a), x) == True{} : Bool}:
  match sub:
    case Nil{}:
      {==}
    case Con{+l, +rest}:
      %Equal.sym(Maybe<&2, TChoice.Clash>, TChoice.clash.at(all, l, a), cf.mk(a, cf.w(all, l, a)), cf.ca(all, l, a)) : {ThemePick.th.clash.above(TChoice.clash.cons(_, TChoice.clashes.go(all, rest, 1n+a)), x) == True{} : Bool}
      cf.above_m(cf.w(all, l, a), a, TChoice.clashes.go(all, rest, 1n+a), x, lt, cf.above(all, rest, 1n+a, x, BO.bo.lt_succ(x, a, lt)))

def cf.rising_m(mw: Maybe<&2, Nat>, +at: Nat, +r: List<&2, TChoice.Clash>, ha: {ThemePick.th.clash.above(r, at) == True{} : Bool}, ih: {ThemePick.th.clash.rising(r) == True{} : Bool}) -> {ThemePick.th.clash.rising(TChoice.clash.cons(cf.mk(at, mw), r)) == True{} : Bool}:
  match mw:
    case None{}:
      ih
    case Some{w0}:
      LT.themes.pt.and_t(ThemePick.th.clash.above(r, at), ThemePick.th.clash.rising(r), ha, ih)

def cf.rising(+all: List<&2, TChoice.Ld>, sub: List<&2, TChoice.Ld>, +at: Nat) -> {ThemePick.th.clash.rising(TChoice.clashes.go(all, sub, at)) == True{} : Bool}:
  match sub:
    case Nil{}:
      {==}
    case Con{+l, +rest}:
      %Equal.sym(Maybe<&2, TChoice.Clash>, TChoice.clash.at(all, l, at), cf.mk(at, cf.w(all, l, at)), cf.ca(all, l, at)) : {ThemePick.th.clash.rising(TChoice.clash.cons(_, TChoice.clashes.go(all, rest, 1n+at))) == True{} : Bool}
      cf.rising_m(cf.w(all, l, at), at, TChoice.clashes.go(all, rest, 1n+at), cf.above(all, rest, 1n+at, at, BO.bo.lt_self(at)), cf.rising(all, rest, 1n+at))

# The law
# -------

def cf.go(r: TName.Res, +ls: List<&2, TChoice.Ld>, +n: String, +i: Nat, +w: Nat)
  -> {ThemePick.th.clash.in(ThemePick.th.clashes.of(TChoice.pick.go(r, ls, n)), i, w) == ThemePick.th.clash.ok(ls, i, w) : Bool} & {ThemePick.th.clash.rising(ThemePick.th.clashes.of(TChoice.pick.go(r, ls, n))) == True{} : Bool}:
  match r:
    case TName.Res{id, wd}:
      match wd:
        case True{}:
          (cf.mem(ls, ls, 0n, i, w, cf.drop0(ls)), cf.rising(ls, ls, 0n))
        case False{}:
          (cf.mem(ls, ls, 0n, i, w, cf.drop0(ls)), cf.rising(ls, ls, 0n))

def ThemePick.theme_pick_clashes_first(ls, n, i, w):
  cf.go(TChoice.pick.res(ls, n), ls, n, i, w)
