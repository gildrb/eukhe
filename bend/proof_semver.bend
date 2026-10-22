# proof_semver: the R1 laws (laws/release.bend, release versions) of the
# model in bend/semver.bend.
#
# Numbers: incrementing the digits adds one to their value, so the digits
# Num.dec writes for n have the value n; Num.read takes them back, as they
# are the digits of their own value. Num.str writes digits that Sym.of
# reads back as those digits, so reading Ver.show(v) gives back the three
# fields of v. The order compares major, then minor, then patch: each
# level is reflexive, transitive, total and antisymmetric when the level
# below it is. The next release takes 1 + a patch at least as high as the
# patch of each tag of the series, under the same major and minor, so it
# is newer than each; a tag of another series never names it, and adds no
# patch to the highest one. A release passed its guard: it is newer than
# every version tag; with only tags of the series, the guard passes.
#
# A recursive proof takes the value it inspects as a parameter (Bend
# matches only parameters), with an equation that names it.

import Base
import ./semver.bend as Sv
import ../laws/release.bend as Release

# Logic
# -----

def ps.BD(b: Bool, t: Type, f: Type) -> Type:
  match b:
    case True{}:
      t
    case False{}:
      f

def ps.absurd(-A: Type, e: {True{} == False{} : Bool}) -> A:
  %e : ps.BD(_, Unit, A)
  Unit{}

def ps.absurdF(-A: Type, e: {False{} == True{} : Bool}) -> A:
  %e : ps.BD(_, A, Unit)
  Unit{}

def ps.MD(m: Maybe<&2, Sv.Ver>, t: Type, f: Type) -> Type:
  match m:
    case None{}:
      t
    case Some{v}:
      f

# None is no Some
def ps.none_some(-A: Type, -r: Sv.Ver, e: {None{} == Some{r} : Maybe<&2, Sv.Ver>}) -> A:
  %e : ps.MD(_, Unit, A)
  Unit{}

def ps.and_l(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      ps.absurdF({False{} == True{} : Bool}, h)

def ps.and_r(a: Bool, +b: Bool, h: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      h
    case False{}:
      ps.absurdF({b == True{} : Bool}, h)

def ps.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      ps.absurdF({True{} == False{} : Bool}, h)
    case False{}:
      {==}

def ps.eq_refl(k: Nat) -> {True{} == Nat.is_eq(k, k) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      ps.eq_refl(p)

def ps.eq_true(a: Nat, b: Nat, h: {Nat.is_eq(a, b) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ps.absurdF({0n == 1n+q : Nat}, h)
    case 1n+p 0n:
      ps.absurdF({1n+p == 0n : Nat}, h)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, ps.eq_true(p, q, h))

# Numbers
# -------

def ps.app_nil(ds: List<&2, Sv.Dig>) -> {ds == List.append(&2, Sv.Dig, ds, Nil{}) : List<&2, Sv.Dig>}:
  match ds:
    case Nil{}:
      {==}
    case +d <> +r:
      Equal.cong(List<&2, Sv.Dig>, List<&2, Sv.Dig>, xs => d <> xs, r, List.append(&2, Sv.Dig, r, Nil{}), ps.app_nil(r))

# incrementing the digits adds one to their value
def ps.val_inc(ds: List<&2, Sv.Dig>) -> {1n+Sv.Num.val(ds) == Sv.Num.val(Sv.Num.inc(ds)) : Nat}:
  match ds:
    case Nil{}:
      {==}
    case d <> rest:
      match d:
        case Sv.D0{}:
          {==}
        case Sv.D1{}:
          {==}
        case Sv.D2{}:
          {==}
        case Sv.D3{}:
          {==}
        case Sv.D4{}:
          {==}
        case Sv.D5{}:
          {==}
        case Sv.D6{}:
          {==}
        case Sv.D7{}:
          {==}
        case Sv.D8{}:
          {==}
        case Sv.D9{}:
          %ps.val_inc(rest) : {1n+Nat.add(9n, Sv.Num.ten(Sv.Num.val(rest))) == Sv.Num.ten(_) : Nat}
          {==}

# the digits of n have the value n
def ps.val_dec(+n: Nat) -> {n == Sv.Num.val(Sv.Num.dec(n)) : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      %ps.val_inc(Sv.Num.dec(p)) : {1n+p == _ : Nat}
      %ps.val_dec(p) : {1n+p == 1n+_ : Nat}
      {==}

def ps.digs_refl(+ds: List<&2, Sv.Dig>) -> {True{} == Sv.Num.digs_eq(ds, ds) : Bool}:
  match ds:
    case Nil{}:
      {==}
    case d <> r:
      %ps.eq_refl(Sv.Dig.val(d)) : {True{} == Bool.and(_, Sv.Num.digs_eq(r, r)) : Bool}
      ps.digs_refl(r)

# Num.read takes back the digits Num.dec writes
def ps.read_dec(+n: Nat) -> {Some{n} == Sv.Num.read(Sv.Num.dec(n)) : Maybe<&2, Nat>}:
  %ps.val_dec(n) : {Some{n} == Sv.Num.read.ok(_, Sv.Num.digs_eq(Sv.Num.dec(_), Sv.Num.dec(n))) : Maybe<&2, Nat>}
  %ps.digs_refl(Sv.Num.dec(n)) : {Some{n} == Sv.Num.read.ok(n, _) : Maybe<&2, Nat>}
  {==}

# Reading
# -------

def ps.sym_chr(d: Sv.Dig) -> {Sv.Sym.of(Sv.Dig.chr(d)) == Sv.Digit{d} : Sv.Sym}:
  match d:
    case Sv.D0{}:
      {==}
    case Sv.D1{}:
      {==}
    case Sv.D2{}:
      {==}
    case Sv.D3{}:
      {==}
    case Sv.D4{}:
      {==}
    case Sv.D5{}:
      {==}
    case Sv.D6{}:
      {==}
    case Sv.D7{}:
      {==}
    case Sv.D8{}:
      {==}
    case Sv.D9{}:
      {==}

# reading the digits Num.str writes before s adds them to the field
def ps.str_read(+ds: List<&2, Sv.Dig>, +s: String, +cur: List<&2, Sv.Dig>, +fs: List<&2, List<&2, Sv.Dig>>) -> {Sv.Ver.fields(Sv.Sym.list(s), List.append(&2, Sv.Dig, ds, cur), fs) == Sv.Ver.fields(Sv.Sym.list(Sv.Num.str(ds, s)), cur, fs) : Maybe<&2, List<&2, List<&2, Sv.Dig>>>}:
  match ds:
    case Nil{}:
      {==}
    case d <> rest:
      %ps.sym_chr(d) : {Sv.Ver.fields(_ <> Sv.Sym.list(s), List.append(&2, Sv.Dig, rest, cur), fs) == Sv.Ver.fields(Sv.Sym.list(Sv.Num.str(rest, SCon{Sv.Dig.chr(d), s})), cur, fs) : Maybe<&2, List<&2, List<&2, Sv.Dig>>>}
      ps.str_read(rest, SCon{Sv.Dig.chr(d), s}, cur, fs)

# parse(show(v)) is v
def ps.roundtrip(v: Sv.Ver) -> {Sv.Ver.parse(Sv.Ver.show(v)) == Some{v} : Maybe<&2, Sv.Ver>}:
  match v:
    case Sv.Ver{+a, +b, +c}:
      %ps.str_read(Sv.Num.dec(a), SCon{'.', Sv.Num.str(Sv.Num.dec(b), SCon{'.', Sv.Num.str(Sv.Num.dec(c), SNil{})})}, Nil{}, Nil{}) : {Sv.Ver.of_fields(_) == Some{Sv.Ver{a, b, c}} : Maybe<&2, Sv.Ver>}
      %ps.str_read(Sv.Num.dec(b), SCon{'.', Sv.Num.str(Sv.Num.dec(c), SNil{})}, Nil{}, [List.append(&2, Sv.Dig, Sv.Num.dec(a), Nil{})]) : {Sv.Ver.of_fields(_) == Some{Sv.Ver{a, b, c}} : Maybe<&2, Sv.Ver>}
      %ps.str_read(Sv.Num.dec(c), SNil{}, Nil{}, [List.append(&2, Sv.Dig, Sv.Num.dec(b), Nil{}), List.append(&2, Sv.Dig, Sv.Num.dec(a), Nil{})]) : {Sv.Ver.of_fields(_) == Some{Sv.Ver{a, b, c}} : Maybe<&2, Sv.Ver>}
      %ps.app_nil(Sv.Num.dec(a)) : {Sv.Ver.of3(Sv.Num.read(_), Sv.Num.read(List.append(&2, Sv.Dig, Sv.Num.dec(b), Nil{})), Sv.Num.read(List.append(&2, Sv.Dig, Sv.Num.dec(c), Nil{}))) == Some{Sv.Ver{a, b, c}} : Maybe<&2, Sv.Ver>}
      %ps.app_nil(Sv.Num.dec(b)) : {Sv.Ver.of3(Sv.Num.read(Sv.Num.dec(a)), Sv.Num.read(_), Sv.Num.read(List.append(&2, Sv.Dig, Sv.Num.dec(c), Nil{}))) == Some{Sv.Ver{a, b, c}} : Maybe<&2, Sv.Ver>}
      %ps.app_nil(Sv.Num.dec(c)) : {Sv.Ver.of3(Sv.Num.read(Sv.Num.dec(a)), Sv.Num.read(Sv.Num.dec(b)), Sv.Num.read(_)) == Some{Sv.Ver{a, b, c}} : Maybe<&2, Sv.Ver>}
      %ps.read_dec(a) : {Sv.Ver.of3(_, Sv.Num.read(Sv.Num.dec(b)), Sv.Num.read(Sv.Num.dec(c))) == Some{Sv.Ver{a, b, c}} : Maybe<&2, Sv.Ver>}
      %ps.read_dec(b) : {Sv.Ver.of3(Some{a}, _, Sv.Num.read(Sv.Num.dec(c))) == Some{Sv.Ver{a, b, c}} : Maybe<&2, Sv.Ver>}
      %ps.read_dec(c) : {Sv.Ver.of3(Some{a}, Some{b}, _) == Some{Sv.Ver{a, b, c}} : Maybe<&2, Sv.Ver>}
      {==}

# The order
# ---------

def ps.num_refl(a: Nat) -> {Sv.Num.le(a, a) == True{} : Bool}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      ps.num_refl(p)

def ps.num_trans(a: Nat, b: Nat, c: Nat, h1: {Sv.Num.le(a, b) == True{} : Bool}, h2: {Sv.Num.le(b, c) == True{} : Bool}) -> {Sv.Num.le(a, c) == True{} : Bool}:
  match a b c:
    case 0n _ _:
      {==}
    case 1n+p 0n _:
      ps.absurdF({Sv.Num.le(1n+p, c) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      ps.absurdF({False{} == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      ps.num_trans(p, q, r, h1, h2)

def ps.num_total(a: Nat, b: Nat) -> {Bool.or(Sv.Num.le(a, b), Sv.Num.le(b, a)) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ps.num_total(p, q)

def ps.num_anti(a: Nat, b: Nat, h1: {Sv.Num.le(a, b) == True{} : Bool}, h2: {Sv.Num.le(b, a) == True{} : Bool}) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      ps.absurdF({0n == 1n+q : Nat}, h2)
    case 1n+p 0n:
      ps.absurdF({1n+p == 0n : Nat}, h1)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, n => 1n+n, p, q, ps.num_anti(p, q, h1, h2))

def ps.bminor(v: Sv.Ver) -> Sv.Ver:
  match v:
    case Sv.Ver{a, b, c}:
      Sv.Ver{a, 1n+b, c}

def ps.bmajor(v: Sv.Ver) -> Sv.Ver:
  match v:
    case Sv.Ver{a, b, c}:
      Sv.Ver{1n+a, b, c}

def ps.le2_refl(b: Nat, +c: Nat) -> {Sv.Ver.le2(b, b, c, c) == True{} : Bool}:
  match b:
    case 0n:
      ps.num_refl(c)
    case 1n+p:
      ps.le2_refl(p, c)

def ps.le2_trans(b1: Nat, b2: Nat, b3: Nat, +c1: Nat, +c2: Nat, +c3: Nat, h1: {Sv.Ver.le2(b1, b2, c1, c2) == True{} : Bool}, h2: {Sv.Ver.le2(b2, b3, c2, c3) == True{} : Bool}) -> {Sv.Ver.le2(b1, b3, c1, c3) == True{} : Bool}:
  match b1 b2 b3:
    case 0n 0n 0n:
      ps.num_trans(c1, c2, c3, h1, h2)
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      ps.absurdF({Sv.Num.le(c1, c3) == True{} : Bool}, h2)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      ps.absurdF({Sv.Ver.le2(1n+p, b3, c1, c3) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      ps.absurdF({False{} == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      ps.le2_trans(p, q, r, c1, c2, c3, h1, h2)

def ps.le2_total(b1: Nat, b2: Nat, +c1: Nat, +c2: Nat) -> {Bool.or(Sv.Ver.le2(b1, b2, c1, c2), Sv.Ver.le2(b2, b1, c2, c1)) == True{} : Bool}:
  match b1 b2:
    case 0n 0n:
      ps.num_total(c1, c2)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ps.le2_total(p, q, c1, c2)

def ps.le2_anti(-a: Nat, b1: Nat, b2: Nat, +c1: Nat, +c2: Nat, h1: {Sv.Ver.le2(b1, b2, c1, c2) == True{} : Bool}, h2: {Sv.Ver.le2(b2, b1, c2, c1) == True{} : Bool}) -> {Sv.Ver{a, b1, c1} == Sv.Ver{a, b2, c2} : Sv.Ver}:
  match b1 b2:
    case 0n 0n:
      Equal.cong(Nat, Sv.Ver, x => Sv.Ver{a, 0n, x}, c1, c2, ps.num_anti(c1, c2, h1, h2))
    case 0n 1n+q:
      ps.absurdF({Sv.Ver{a, 0n, c1} == Sv.Ver{a, 1n+q, c2} : Sv.Ver}, h2)
    case 1n+p 0n:
      ps.absurdF({Sv.Ver{a, 1n+p, c1} == Sv.Ver{a, 0n, c2} : Sv.Ver}, h1)
    case 1n+p 1n+q:
      Equal.cong(Sv.Ver, Sv.Ver, ps.bminor, Sv.Ver{a, p, c1}, Sv.Ver{a, q, c2}, ps.le2_anti(a, p, q, c1, c2, h1, h2))

def ps.le3_refl(a: Nat, +b: Nat, +c: Nat) -> {Sv.Ver.le3(a, a, b, b, c, c) == True{} : Bool}:
  match a:
    case 0n:
      ps.le2_refl(b, c)
    case 1n+p:
      ps.le3_refl(p, b, c)

def ps.le3_trans(a1: Nat, a2: Nat, a3: Nat, +b1: Nat, +b2: Nat, +b3: Nat, +c1: Nat, +c2: Nat, +c3: Nat, h1: {Sv.Ver.le3(a1, a2, b1, b2, c1, c2) == True{} : Bool}, h2: {Sv.Ver.le3(a2, a3, b2, b3, c2, c3) == True{} : Bool}) -> {Sv.Ver.le3(a1, a3, b1, b3, c1, c3) == True{} : Bool}:
  match a1 a2 a3:
    case 0n 0n 0n:
      ps.le2_trans(b1, b2, b3, c1, c2, c3, h1, h2)
    case 0n 0n 1n+r:
      {==}
    case 0n 1n+q 0n:
      ps.absurdF({Sv.Ver.le2(b1, b3, c1, c3) == True{} : Bool}, h2)
    case 0n 1n+q 1n+r:
      {==}
    case 1n+p 0n _:
      ps.absurdF({Sv.Ver.le3(1n+p, a3, b1, b3, c1, c3) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      ps.absurdF({False{} == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      ps.le3_trans(p, q, r, b1, b2, b3, c1, c2, c3, h1, h2)

def ps.le3_total(a1: Nat, a2: Nat, +b1: Nat, +b2: Nat, +c1: Nat, +c2: Nat) -> {Bool.or(Sv.Ver.le3(a1, a2, b1, b2, c1, c2), Sv.Ver.le3(a2, a1, b2, b1, c2, c1)) == True{} : Bool}:
  match a1 a2:
    case 0n 0n:
      ps.le2_total(b1, b2, c1, c2)
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ps.le3_total(p, q, b1, b2, c1, c2)

def ps.le3_anti(a1: Nat, a2: Nat, +b1: Nat, +b2: Nat, +c1: Nat, +c2: Nat, h1: {Sv.Ver.le3(a1, a2, b1, b2, c1, c2) == True{} : Bool}, h2: {Sv.Ver.le3(a2, a1, b2, b1, c2, c1) == True{} : Bool}) -> {Sv.Ver{a1, b1, c1} == Sv.Ver{a2, b2, c2} : Sv.Ver}:
  match a1 a2:
    case 0n 0n:
      ps.le2_anti(0n, b1, b2, c1, c2, h1, h2)
    case 0n 1n+q:
      ps.absurdF({Sv.Ver{0n, b1, c1} == Sv.Ver{1n+q, b2, c2} : Sv.Ver}, h2)
    case 1n+p 0n:
      ps.absurdF({Sv.Ver{1n+p, b1, c1} == Sv.Ver{0n, b2, c2} : Sv.Ver}, h1)
    case 1n+p 1n+q:
      Equal.cong(Sv.Ver, Sv.Ver, ps.bmajor, Sv.Ver{p, b1, c1}, Sv.Ver{q, b2, c2}, ps.le3_anti(p, q, b1, b2, c1, c2, h1, h2))

def ps.le_refl(v: Sv.Ver) -> {Sv.Ver.le(v, v) == True{} : Bool}:
  match v:
    case Sv.Ver{+a, +b, +c}:
      ps.le3_refl(a, b, c)

def ps.le_trans(u: Sv.Ver, v: Sv.Ver, w: Sv.Ver, h1: {Sv.Ver.le(u, v) == True{} : Bool}, h2: {Sv.Ver.le(v, w) == True{} : Bool}) -> {Sv.Ver.le(u, w) == True{} : Bool}:
  match u v w:
    case Sv.Ver{a1, b1, c1} Sv.Ver{a2, b2, c2} Sv.Ver{a3, b3, c3}:
      ps.le3_trans(a1, a2, a3, b1, b2, b3, c1, c2, c3, h1, h2)

def ps.le_total(u: Sv.Ver, v: Sv.Ver) -> {Bool.or(Sv.Ver.le(u, v), Sv.Ver.le(v, u)) == True{} : Bool}:
  match u v:
    case Sv.Ver{a1, b1, c1} Sv.Ver{a2, b2, c2}:
      ps.le3_total(a1, a2, b1, b2, c1, c2)

def ps.le_anti(u: Sv.Ver, v: Sv.Ver, h1: {Sv.Ver.le(u, v) == True{} : Bool}, h2: {Sv.Ver.le(v, u) == True{} : Bool}) -> {u == v : Sv.Ver}:
  match u v:
    case Sv.Ver{a1, b1, c1} Sv.Ver{a2, b2, c2}:
      ps.le3_anti(a1, a2, b1, b2, c1, c2, h1, h2)

# no version is newer than itself
def ps.lt_irrefl(+v: Sv.Ver) -> {False{} == Sv.Ver.lt(v, v) : Bool}:
  %Equal.sym(Bool, Sv.Ver.le(v, v), True{}, ps.le_refl(v)) : {False{} == Bool.not(_) : Bool}
  {==}

# a version newer than u is not u
def ps.lt_ne(+u: Sv.Ver, -w: Sv.Ver, h: {Sv.Ver.lt(u, w) == True{} : Bool}, e: {u == w : Sv.Ver}) -> Empty:
  +self = Equal.cong(Sv.Ver, Bool, x => Sv.Ver.lt(u, x), u, w, e)
  ps.absurdF(Empty, Equal.trans(Bool, False{}, Sv.Ver.lt(u, w), True{}, Equal.trans(Bool, False{}, Sv.Ver.lt(u, u), Sv.Ver.lt(u, w), ps.lt_irrefl(u), self), h))

# The next release
# ----------------

def ps.app_snoc(xs: List<&2, String>, +a: String, +ys: List<&2, String>) -> {List.append(&2, String, List.append(&2, String, xs, [a]), ys) == List.append(&2, String, xs, a <> ys) : List<&2, String>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      Equal.cong(List<&2, String>, List<&2, String>, zs => x <> zs, List.append(&2, String, List.append(&2, String, r, [a]), ys), List.append(&2, String, r, a <> ys), ps.app_snoc(r, a, ys))

# m names a number of at least p
def ps.atl(p: Nat, m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{q}:
      Sv.Num.le(p, q)

def ps.le_max_l(a: Nat, b: Nat) -> {Sv.Num.le(a, Sv.Num.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n _:
      {==}
    case 1n+p 0n:
      ps.num_refl(p)
    case 1n+p 1n+q:
      ps.le_max_l(p, q)

def ps.le_max_r(a: Nat, b: Nat) -> {Sv.Num.le(b, Sv.Num.max(a, b)) == True{} : Bool}:
  match a b:
    case 0n _:
      ps.num_refl(b)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      ps.le_max_r(p, q)

def ps.atl_max(+p: Nat, acc: Maybe<&2, Nat>) -> {ps.atl(p, Sv.Rel.max(p, acc)) == True{} : Bool}:
  match acc:
    case None{}:
      ps.num_refl(p)
    case Some{q}:
      ps.le_max_l(p, q)

def ps.atl_keep(+p: Nat, b: Bool, +q: Nat, acc: Maybe<&2, Nat>, h: {ps.atl(p, acc) == True{} : Bool}) -> {ps.atl(p, Sv.Rel.keep(b, q, acc)) == True{} : Bool}:
  match b:
    case True{}:
      match acc:
        case None{}:
          ps.absurdF({ps.atl(p, Sv.Rel.max(q, None{})) == True{} : Bool}, h)
        case Some{+r}:
          ps.num_trans(p, r, Sv.Num.max(q, r), h, ps.le_max_r(q, r))
    case False{}:
      h

def ps.atl_add(+p: Nat, +s: Sv.Ver, m: Maybe<&2, Sv.Ver>, acc: Maybe<&2, Nat>, h: {ps.atl(p, acc) == True{} : Bool}) -> {ps.atl(p, Sv.Rel.add(s, m, acc)) == True{} : Bool}:
  match m:
    case None{}:
      h
    case Some{+v}:
      ps.atl_keep(p, Sv.Ver.in_series(s, v), Sv.Ver.patch(v), acc, h)

# with tag t of the series among the tags, the highest patch is at least
# the patch of t
def ps.top_mid(+s: Sv.Ver, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, +v: Sv.Ver, parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}, ins: {Sv.Ver.in_series(s, v) == True{} : Bool}) -> {ps.atl(Sv.Ver.patch(v), Sv.Rel.top(s, List.append(&2, String, xs, t <> ys))) == True{} : Bool}:
  match xs:
    case Nil{}:
      %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Tag.ver(t), Some{v}, parsed) : {ps.atl(Sv.Ver.patch(v), Sv.Rel.add(s, _, Sv.Rel.top(s, ys))) == True{} : Bool}
      %Equal.sym(Bool, Sv.Ver.in_series(s, v), True{}, ins) : {ps.atl(Sv.Ver.patch(v), Sv.Rel.keep(_, Sv.Ver.patch(v), Sv.Rel.top(s, ys))) == True{} : Bool}
      ps.atl_max(Sv.Ver.patch(v), Sv.Rel.top(s, ys))
    case +x <> +r:
      ps.atl_add(Sv.Ver.patch(v), s, Sv.Tag.ver(x), Sv.Rel.top(s, List.append(&2, String, r, t <> ys)), ps.top_mid(s, r, t, ys, v, parsed, ins))

def ps.le_succ(p: Nat, q: Nat, h: {Sv.Num.le(p, q) == True{} : Bool}) -> {Sv.Num.le(1n+q, p) == False{} : Bool}:
  match p q:
    case 0n _:
      {==}
    case 1n+a 0n:
      ps.absurdF({Sv.Num.le(1n+0n, 1n+a) == False{} : Bool}, h)
    case 1n+a 1n+b:
      ps.le_succ(a, b, h)

def ps.after_gt(+p: Nat, m: Maybe<&2, Nat>, h: {ps.atl(p, m) == True{} : Bool}) -> {Sv.Num.le(Sv.Rel.after(m), p) == False{} : Bool}:
  match m:
    case None{}:
      ps.absurdF({Sv.Num.le(0n, p) == False{} : Bool}, h)
    case Some{q}:
      ps.le_succ(p, q, h)

def ps.le2_same(b: Nat, +x: Nat, +y: Nat) -> {Sv.Num.le(x, y) == Sv.Ver.le2(b, b, x, y) : Bool}:
  match b:
    case 0n:
      {==}
    case 1n+p:
      ps.le2_same(p, x, y)

def ps.le3_same(a: Nat, +b: Nat, +x: Nat, +y: Nat) -> {Sv.Num.le(x, y) == Sv.Ver.le3(a, a, b, b, x, y) : Bool}:
  match a:
    case 0n:
      ps.le2_same(b, x, y)
    case 1n+p:
      ps.le3_same(p, b, x, y)

# the next release is newer than each tag of the series
def ps.next_newer(s: Sv.Ver, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, v: Sv.Ver, parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}, +ins: {Sv.Ver.in_series(s, v) == True{} : Bool}) -> {Sv.Ver.lt(v, Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))) == True{} : Bool}:
  match s v:
    case Sv.Ver{+a, +b, +c} Sv.Ver{+va, +vb, +vc}:
      %ps.eq_true(a, va, ps.and_l(Nat.is_eq(a, va), Nat.is_eq(b, vb), ins)) : {Bool.not(Sv.Ver.le3(a, _, b, vb, Sv.Rel.after(Sv.Rel.top(Sv.Ver{a, b, c}, List.append(&2, String, xs, t <> ys))), vc)) == True{} : Bool}
      %ps.eq_true(b, vb, ps.and_r(Nat.is_eq(a, va), Nat.is_eq(b, vb), ins)) : {Bool.not(Sv.Ver.le3(a, a, b, _, Sv.Rel.after(Sv.Rel.top(Sv.Ver{a, b, c}, List.append(&2, String, xs, t <> ys))), vc)) == True{} : Bool}
      %ps.le3_same(a, b, Sv.Rel.after(Sv.Rel.top(Sv.Ver{a, b, c}, List.append(&2, String, xs, t <> ys))), vc) : {Bool.not(_) == True{} : Bool}
      %Equal.sym(Bool, Sv.Num.le(Sv.Rel.after(Sv.Rel.top(Sv.Ver{a, b, c}, List.append(&2, String, xs, t <> ys))), vc), False{}, ps.after_gt(vc, Sv.Rel.top(Sv.Ver{a, b, c}, List.append(&2, String, xs, t <> ys)), ps.top_mid(Sv.Ver{a, b, c}, xs, t, ys, Sv.Ver{va, vb, vc}, parsed, ins))) : {Bool.not(_) == True{} : Bool}
      {==}

# the next release is of the series
def ps.series_next(s: Sv.Ver, tags: List<&2, String>) -> {Sv.Ver.in_series(s, Sv.Rel.next(s, tags)) == True{} : Bool}:
  match s:
    case Sv.Ver{+a, +b, c}:
      %ps.eq_refl(a) : {Bool.and(_, Nat.is_eq(b, b)) == True{} : Bool}
      Equal.sym(Bool, True{}, Nat.is_eq(b, b), ps.eq_refl(b))

def ps.next_ne.go(+s: Sv.Ver, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, +v: Sv.Ver, parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}, b: Bool, eb: {Sv.Ver.in_series(s, v) == b : Bool}, e: {v == Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)) : Sv.Ver}) -> Empty:
  match b:
    case True{}:
      ps.lt_ne(v, Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)), ps.next_newer(s, xs, t, ys, v, parsed, eb), e)
    case False{}:
      +same = Equal.cong(Sv.Ver, Bool, x => Sv.Ver.in_series(s, x), v, Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)), e)
      +into = Equal.trans(Bool, Sv.Ver.in_series(s, v), Sv.Ver.in_series(s, Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))), True{}, same, ps.series_next(s, List.append(&2, String, xs, t <> ys)))
      ps.absurdF(Empty, Equal.trans(Bool, False{}, Sv.Ver.in_series(s, v), True{}, Equal.sym(Bool, Sv.Ver.in_series(s, v), False{}, eb), into))

# no version tag names the next release
def ps.next_ne(+s: Sv.Ver, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, +v: Sv.Ver, parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}) -> {v != Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)) : Sv.Ver}:
  e => ps.next_ne.go(s, xs, t, ys, v, parsed, Sv.Ver.in_series(s, v), {==}, e)

def ps.tag_new.go(+s: Sv.Ver, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, e: {Sv.Tag.of(Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))) == t : String}) -> Empty:
  +n = Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))
  +back = Equal.cong(String, Maybe<&2, Sv.Ver>, Sv.Tag.ver, Sv.Tag.of(n), t, e)
  +parsed = Equal.trans(Maybe<&2, Sv.Ver>, Sv.Tag.ver(t), Sv.Tag.ver(Sv.Tag.of(n)), Some{n}, Equal.sym(Maybe<&2, Sv.Ver>, Sv.Tag.ver(Sv.Tag.of(n)), Sv.Tag.ver(t), back), ps.roundtrip(n))
  ps.next_ne(s, xs, t, ys, n, parsed)({==})

# no tag is the tag of the next release
def ps.tag_new(+s: Sv.Ver, +xs: List<&2, String>, +t: String, +ys: List<&2, String>) -> {Sv.Tag.of(Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))) != t : String}:
  e => ps.tag_new.go(s, xs, t, ys, e)

# a fresh series starts at patch 0
def ps.add_skip(+s: Sv.Ver, m: Maybe<&2, Sv.Ver>, +acc: Maybe<&2, Nat>, h: {Sv.Rel.ofs.of(s, m) == False{} : Bool}) -> {acc == Sv.Rel.add(s, m, acc) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{+w}:
      %Equal.sym(Bool, Sv.Ver.in_series(s, w), False{}, h) : {acc == Sv.Rel.keep(_, Sv.Ver.patch(w), acc) : Maybe<&2, Nat>}
      {==}

def ps.top_none(+s: Sv.Ver, tags: List<&2, String>, +h: {Sv.Rel.none(s, tags) == True{} : Bool}) -> {None{} == Sv.Rel.top(s, tags) : Maybe<&2, Nat>}:
  match tags:
    case Nil{}:
      {==}
    case +t <> +r:
      %ps.top_none(s, r, ps.and_r(Bool.not(Sv.Rel.ofs(s, t)), Sv.Rel.none(s, r), h)) : {None{} == Sv.Rel.add(s, Sv.Tag.ver(t), _) : Maybe<&2, Nat>}
      ps.add_skip(s, Sv.Tag.ver(t), None{}, ps.not_t(Sv.Rel.ofs(s, t), ps.and_l(Bool.not(Sv.Rel.ofs(s, t)), Sv.Rel.none(s, r), h)))

def ps.fresh(+a: Nat, +b: Nat, +c: Nat, +tags: List<&2, String>, none: {Sv.Rel.none(Sv.Ver{a, b, c}, tags) == True{} : Bool}) -> {Sv.Rel.next(Sv.Ver{a, b, c}, tags) == Sv.Ver{a, b, 0n} : Sv.Ver}:
  %ps.top_none(Sv.Ver{a, b, c}, tags, none) : {Sv.Ver{a, b, Sv.Rel.after(_)} == Sv.Ver{a, b, 0n} : Sv.Ver}
  {==}

# a tag of another series changes nothing
def ps.top_skip(+s: Sv.Ver, xs: List<&2, String>, +t: String, +ys: List<&2, String>, h: {Sv.Rel.ofs(s, t) == False{} : Bool}) -> {Sv.Rel.top(s, List.append(&2, String, xs, ys)) == Sv.Rel.top(s, List.append(&2, String, xs, t <> ys)) : Maybe<&2, Nat>}:
  match xs:
    case Nil{}:
      ps.add_skip(s, Sv.Tag.ver(t), Sv.Rel.top(s, ys), h)
    case x <> r:
      %ps.top_skip(s, r, t, ys, h) : {Sv.Rel.add(s, Sv.Tag.ver(x), Sv.Rel.top(s, List.append(&2, String, r, ys))) == Sv.Rel.add(s, Sv.Tag.ver(x), _) : Maybe<&2, Nat>}
      {==}

def ps.other(s: Sv.Ver, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, h: {Sv.Rel.ofs(s, t) == False{} : Bool}) -> {Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)) == Sv.Rel.next(s, List.append(&2, String, xs, ys)) : Sv.Ver}:
  match s:
    case Sv.Ver{+a, +b, +c}:
      %ps.top_skip(Sv.Ver{a, b, c}, xs, t, ys, h) : {Sv.Ver{a, b, Sv.Rel.after(_)} == Sv.Ver{a, b, Sv.Rel.after(Sv.Rel.top(Sv.Ver{a, b, c}, List.append(&2, String, xs, ys)))} : Sv.Ver}
      {==}

# A release
# ---------

def ps.guard_ok(ok: Bool, -n: Sv.Ver, -r: Sv.Ver, h: {Sv.Rel.guard(ok, n) == Some{r} : Maybe<&2, Sv.Ver>}) -> {ok == True{} : Bool}:
  match ok:
    case True{}:
      {==}
    case False{}:
      ps.none_some({False{} == True{} : Bool}, r, h)

def ps.guard_val(ok: Bool, +n: Sv.Ver, -r: Sv.Ver, h: {Sv.Rel.guard(ok, n) == Some{r} : Maybe<&2, Sv.Ver>}) -> {n == r : Sv.Ver}:
  match ok:
    case True{}:
      Equal.cong(Maybe<&2, Sv.Ver>, Sv.Ver, m => Maybe.default(&2, Sv.Ver, m, n), Some{n}, Some{r}, h)
    case False{}:
      ps.none_some({n == r : Sv.Ver}, r, h)

def ps.newest_mid(+n: Sv.Ver, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, h: {Sv.Rel.newest(n, List.append(&2, String, xs, t <> ys)) == True{} : Bool}) -> {Sv.Rel.older(n, Sv.Tag.ver(t)) == True{} : Bool}:
  match xs:
    case Nil{}:
      ps.and_l(Sv.Rel.older(n, Sv.Tag.ver(t)), Sv.Rel.newest(n, ys), h)
    case +x <> +r:
      ps.newest_mid(n, r, t, ys, ps.and_r(Sv.Rel.older(n, Sv.Tag.ver(x)), Sv.Rel.newest(n, List.append(&2, String, r, t <> ys)), h))

# a release is newer than every version tag
def ps.release_newest(m: Maybe<&2, Sv.Ver>, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, -r: Sv.Ver, +rel: {Sv.Rel.release.of(m, List.append(&2, String, xs, t <> ys)) == Some{r} : Maybe<&2, Sv.Ver>}, +v: Sv.Ver, parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}) -> {Sv.Ver.lt(v, r) == True{} : Bool}:
  match m:
    case None{}:
      ps.none_some({Sv.Ver.lt(v, r) == True{} : Bool}, r, rel)
    case Some{w}:
      match w:
        case Sv.Ver{+a, +b, c}:
          match c:
            case 0n:
              +n = Sv.Rel.next(Sv.Ver{a, b, 0n}, List.append(&2, String, xs, t <> ys))
              +ok = ps.guard_ok(Sv.Rel.newest(n, List.append(&2, String, xs, t <> ys)), n, r, rel)
              %ps.guard_val(Sv.Rel.newest(n, List.append(&2, String, xs, t <> ys)), n, r, rel) : {Sv.Ver.lt(v, _) == True{} : Bool}
              %parsed : {Sv.Rel.older(n, _) == True{} : Bool}
              ps.newest_mid(n, xs, t, ys, ok)
            case 1n+p:
              ps.none_some({Sv.Ver.lt(v, r) == True{} : Bool}, r, rel)

def ps.release_newest_of(c: String, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, -r: Sv.Ver, rel: {Sv.Rel.release(c, List.append(&2, String, xs, t <> ys)) == Some{r} : Maybe<&2, Sv.Ver>}, +v: Sv.Ver, parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}) -> {Sv.Ver.lt(v, r) == True{} : Bool}:
  ps.release_newest(Sv.Ver.parse(c), xs, t, ys, r, rel, v, parsed)

def ps.older_of(+s: Sv.Ver, +pre: List<&2, String>, +t: String, +r: List<&2, String>, m: Maybe<&2, Sv.Ver>, em: {Sv.Tag.ver(t) == m : Maybe<&2, Sv.Ver>}, h: {Sv.Rel.only.of(s, m) == True{} : Bool}) -> {True{} == Sv.Rel.older(Sv.Rel.next(s, List.append(&2, String, pre, t <> r)), m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+v}:
      Equal.sym(Bool, Sv.Ver.lt(v, Sv.Rel.next(s, List.append(&2, String, pre, t <> r))), True{}, ps.next_newer(s, pre, t, r, v, em, h))

def ps.newest_only(rest: List<&2, String>, +s: Sv.Ver, +pre: List<&2, String>, +h: {Sv.Rel.only(s, rest) == True{} : Bool}) -> {True{} == Sv.Rel.newest(Sv.Rel.next(s, List.append(&2, String, pre, rest)), rest) : Bool}:
  match rest:
    case Nil{}:
      {==}
    case +t <> +r:
      %ps.older_of(s, pre, t, r, Sv.Tag.ver(t), {==}, ps.and_l(Sv.Rel.only.of(s, Sv.Tag.ver(t)), Sv.Rel.only(s, r), h)) : {True{} == Bool.and(_, Sv.Rel.newest(Sv.Rel.next(s, List.append(&2, String, pre, t <> r)), r)) : Bool}
      %ps.app_snoc(pre, t, r) : {True{} == Sv.Rel.newest(Sv.Rel.next(s, _), r) : Bool}
      ps.newest_only(r, s, List.append(&2, String, pre, [t]), ps.and_r(Sv.Rel.only.of(s, Sv.Tag.ver(t)), Sv.Rel.only(s, r), h))

# with only tags of the series, the workspace version X.Y.0 releases the
# next release
def ps.progress(c: String, +a: Nat, +b: Nat, +tags: List<&2, String>, parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 0n}} : Maybe<&2, Sv.Ver>}, only: {Sv.Rel.only(Sv.Ver{a, b, 0n}, tags) == True{} : Bool}) -> {Sv.Rel.release(c, tags) == Some{Sv.Rel.next(Sv.Ver{a, b, 0n}, tags)} : Maybe<&2, Sv.Ver>}:
  %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Ver.parse(c), Some{Sv.Ver{a, b, 0n}}, parsed) : {Sv.Rel.release.of(_, tags) == Some{Sv.Rel.next(Sv.Ver{a, b, 0n}, tags)} : Maybe<&2, Sv.Ver>}
  %ps.newest_only(tags, Sv.Ver{a, b, 0n}, Nil{}, only) : {Sv.Rel.guard(_, Sv.Rel.next(Sv.Ver{a, b, 0n}, tags)) == Some{Sv.Rel.next(Sv.Ver{a, b, 0n}, tags)} : Maybe<&2, Sv.Ver>}
  {==}

# a workspace version X.Y.(1+z) releases nothing
def ps.refuse_patch(c: String, +a: Nat, +b: Nat, +z: Nat, +tags: List<&2, String>, parsed: {Sv.Ver.parse(c) == Some{Sv.Ver{a, b, 1n+z}} : Maybe<&2, Sv.Ver>}) -> {Sv.Rel.release(c, tags) == None{} : Maybe<&2, Sv.Ver>}:
  %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Ver.parse(c), Some{Sv.Ver{a, b, 1n+z}}, parsed) : {Sv.Rel.release.of(_, tags) == None{} : Maybe<&2, Sv.Ver>}
  {==}

# a workspace version that is no version releases nothing
def ps.refuse_unparsed(c: String, +tags: List<&2, String>, unparsed: {Sv.Ver.parse(c) == None{} : Maybe<&2, Sv.Ver>}) -> {Sv.Rel.release(c, tags) == None{} : Maybe<&2, Sv.Ver>}:
  %Equal.sym(Maybe<&2, Sv.Ver>, Sv.Ver.parse(c), None{}, unparsed) : {Sv.Rel.release.of(_, tags) == None{} : Maybe<&2, Sv.Ver>}
  {==}

# Decimal writing (semver_show_decimal): the spec's writer of the law file
# and the model's Num.str agree.

# digits written before x ++ acc: the digits before x, then acc
def ps.str_app(ds: List<&2, Sv.Dig>, x: String, acc: String) -> {Sv.Num.str(ds, String.append(x, acc)) == String.append(Sv.Num.str(ds, x), acc) : String}:
  match ds:
    case Nil{}:
      {==}
    case d <> rest:
      ps.str_app(rest, SCon{Sv.Dig.chr(d), x}, acc)

# reversing onto acc, then reversing that, gives acc reversed onto s
def ps.rev_rev(s: String, acc: String) -> {String.reverse.go(String.reverse.go(s, acc), SNil{}) == String.reverse.go(acc, s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{h, t}:
      ps.rev_rev(t, SCon{h, acc})

# the digits as text, last digit first
def ps.lsf(ds: List<&2, Sv.Dig>) -> String:
  match ds:
    case Nil{}:
      SNil{}
    case d <> rest:
      SCon{Sv.Dig.chr(d), ps.lsf(rest)}

# writing digits before acc is reversing their text onto acc
def ps.str_rev(ds: List<&2, Sv.Dig>, acc: String) -> {Sv.Num.str(ds, acc) == String.reverse.go(ps.lsf(ds), acc) : String}:
  match ds:
    case Nil{}:
      {==}
    case d <> rest:
      ps.str_rev(rest, SCon{Sv.Dig.chr(d), acc})

# raising the text of digits is the text of the next number's digits
def ps.raise_inc(ds: List<&2, Sv.Dig>) -> {Release.dec_raise(ps.lsf(ds)) == ps.lsf(Sv.Num.inc(ds)) : String}:
  match ds:
    case Nil{}:
      {==}
    case d <> rest:
      match d:
        case Sv.D0{}:
          {==}
        case Sv.D1{}:
          {==}
        case Sv.D2{}:
          {==}
        case Sv.D3{}:
          {==}
        case Sv.D4{}:
          {==}
        case Sv.D5{}:
          {==}
        case Sv.D6{}:
          {==}
        case Sv.D7{}:
          {==}
        case Sv.D8{}:
          {==}
        case Sv.D9{}:
          Equal.cong(String, String, s => SCon{'0', s}, Release.dec_raise(ps.lsf(rest)), ps.lsf(Sv.Num.inc(rest)), ps.raise_inc(rest))

# the spec's decimal text of n is the text Num.str writes for n's digits
def ps.dec_spec_str(n: Nat) -> {Release.dec_spec(n) == Sv.Num.str(Sv.Num.dec(n), SNil{}) : String}:
  match n:
    case 0n:
      {==}
    case 1n+(+p):
      %Equal.sym(String, Release.dec_spec(p), Sv.Num.str(Sv.Num.dec(p), SNil{}), ps.dec_spec_str(p)) : {String.reverse(Release.dec_raise(String.reverse(_))) == Sv.Num.str(Sv.Num.inc(Sv.Num.dec(p)), SNil{}) : String}
      %Equal.sym(String, Sv.Num.str(Sv.Num.dec(p), SNil{}), String.reverse.go(ps.lsf(Sv.Num.dec(p)), SNil{}), ps.str_rev(Sv.Num.dec(p), SNil{})) : {String.reverse(Release.dec_raise(String.reverse(_))) == Sv.Num.str(Sv.Num.inc(Sv.Num.dec(p)), SNil{}) : String}
      %Equal.sym(String, String.reverse.go(String.reverse.go(ps.lsf(Sv.Num.dec(p)), SNil{}), SNil{}), String.reverse.go(SNil{}, ps.lsf(Sv.Num.dec(p))), ps.rev_rev(ps.lsf(Sv.Num.dec(p)), SNil{})) : {String.reverse(Release.dec_raise(_)) == Sv.Num.str(Sv.Num.inc(Sv.Num.dec(p)), SNil{}) : String}
      %Equal.sym(String, Release.dec_raise(ps.lsf(Sv.Num.dec(p))), ps.lsf(Sv.Num.inc(Sv.Num.dec(p))), ps.raise_inc(Sv.Num.dec(p))) : {String.reverse(_) == Sv.Num.str(Sv.Num.inc(Sv.Num.dec(p)), SNil{}) : String}
      Equal.sym(String, Sv.Num.str(Sv.Num.inc(Sv.Num.dec(p)), SNil{}), String.reverse.go(ps.lsf(Sv.Num.inc(Sv.Num.dec(p))), SNil{}), ps.str_rev(Sv.Num.inc(Sv.Num.dec(p)), SNil{}))

# a version is written as its three numbers in decimal, joined by dots
def ps.show_decimal(+a: Nat, +b: Nat, +c: Nat) -> {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(Release.dec_spec(a), SCon{'.', String.append(Release.dec_spec(b), SCon{'.', Release.dec_spec(c)})}) : String}:
  %Equal.sym(String, Release.dec_spec(a), Sv.Num.str(Sv.Num.dec(a), SNil{}), ps.dec_spec_str(a)) : {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(_, SCon{'.', String.append(Release.dec_spec(b), SCon{'.', Release.dec_spec(c)})}) : String}
  %Equal.sym(String, Release.dec_spec(b), Sv.Num.str(Sv.Num.dec(b), SNil{}), ps.dec_spec_str(b)) : {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(Sv.Num.str(Sv.Num.dec(a), SNil{}), SCon{'.', String.append(_, SCon{'.', Release.dec_spec(c)})}) : String}
  %Equal.sym(String, Release.dec_spec(c), Sv.Num.str(Sv.Num.dec(c), SNil{}), ps.dec_spec_str(c)) : {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(Sv.Num.str(Sv.Num.dec(a), SNil{}), SCon{'.', String.append(Sv.Num.str(Sv.Num.dec(b), SNil{}), SCon{'.', _})}) : String}
  %ps.str_app(Sv.Num.dec(b), SNil{}, SCon{'.', Sv.Num.str(Sv.Num.dec(c), SNil{})}) : {Sv.Ver.show(Sv.Ver{a, b, c}) == String.append(Sv.Num.str(Sv.Num.dec(a), SNil{}), SCon{'.', _}) : String}
  ps.str_app(Sv.Num.dec(a), SNil{}, SCon{'.', Sv.Num.str(Sv.Num.dec(b), SCon{'.', Sv.Num.str(Sv.Num.dec(c), SNil{})})})
