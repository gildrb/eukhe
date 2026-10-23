# eukhe: lemmas the proofs of area semver share

import Base
import ../../bend/semver.bend as Sv
import ../base/logic/bool.bend as LLogicBool
import ../base/logic/logic.bend as LLogicLogic
import ../base/logic/nat.bend as LLogicNat
import ../base/nat.bend as LNat
import ../base/semver.bend as LSemver

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

# Num.read takes back the digits Num.dec writes
def ps.read_dec(+n: Nat) -> {Some{n} == Sv.Num.read(Sv.Num.dec(n)) : Maybe<&2, Nat>}:
  %ps.val_dec(n) : {Some{n} == Sv.Num.read.ok(_, Sv.Num.digs_eq(Sv.Num.dec(_), Sv.Num.dec(n))) : Maybe<&2, Nat>}
  %LSemver.ps.digs_refl(Sv.Num.dec(n)) : {Some{n} == Sv.Num.read.ok(n, _) : Maybe<&2, Nat>}
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
      LLogicLogic.semver.ps.absurdF({Sv.Num.le(1n+p, c) == True{} : Bool}, h1)
    case 1n+p 1n+q 0n:
      LLogicLogic.semver.ps.absurdF({False{} == True{} : Bool}, h2)
    case 1n+p 1n+q 1n+r:
      ps.num_trans(p, q, r, h1, h2)

def ps.le2_refl(b: Nat, +c: Nat) -> {Sv.Ver.le2(b, b, c, c) == True{} : Bool}:
  match b:
    case 0n:
      ps.num_refl(c)
    case 1n+p:
      ps.le2_refl(p, c)

def ps.le3_refl(a: Nat, +b: Nat, +c: Nat) -> {Sv.Ver.le3(a, a, b, b, c, c) == True{} : Bool}:
  match a:
    case 0n:
      ps.le2_refl(b, c)
    case 1n+p:
      ps.le3_refl(p, b, c)

def semver.ps.le_refl(v: Sv.Ver) -> {Sv.Ver.le(v, v) == True{} : Bool}:
  match v:
    case Sv.Ver{+a, +b, +c}:
      ps.le3_refl(a, b, c)

# no version is newer than itself
def ps.lt_irrefl(+v: Sv.Ver) -> {False{} == Sv.Ver.lt(v, v) : Bool}:
  %Equal.sym(Bool, Sv.Ver.le(v, v), True{}, semver.ps.le_refl(v)) : {False{} == Bool.not(_) : Bool}
  {==}

# a version newer than u is not u
def ps.lt_ne(+u: Sv.Ver, -w: Sv.Ver, h: {Sv.Ver.lt(u, w) == True{} : Bool}, e: {u == w : Sv.Ver}) -> Empty:
  +self = Equal.cong(Sv.Ver, Bool, x => Sv.Ver.lt(u, x), u, w, e)
  LLogicLogic.semver.ps.absurdF(Empty, Equal.trans(Bool, False{}, Sv.Ver.lt(u, w), True{}, Equal.trans(Bool, False{}, Sv.Ver.lt(u, u), Sv.Ver.lt(u, w), ps.lt_irrefl(u), self), h))

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
          LLogicLogic.semver.ps.absurdF({ps.atl(p, Sv.Rel.max(q, None{})) == True{} : Bool}, h)
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

def semver.ps.le_succ(p: Nat, q: Nat, h: {Sv.Num.le(p, q) == True{} : Bool}) -> {Sv.Num.le(1n+q, p) == False{} : Bool}:
  match p q:
    case 0n _:
      {==}
    case 1n+a 0n:
      LLogicLogic.semver.ps.absurdF({Sv.Num.le(1n+0n, 1n+a) == False{} : Bool}, h)
    case 1n+a 1n+b:
      semver.ps.le_succ(a, b, h)

def ps.after_gt(+p: Nat, m: Maybe<&2, Nat>, h: {ps.atl(p, m) == True{} : Bool}) -> {Sv.Num.le(Sv.Rel.after(m), p) == False{} : Bool}:
  match m:
    case None{}:
      LLogicLogic.semver.ps.absurdF({Sv.Num.le(0n, p) == False{} : Bool}, h)
    case Some{q}:
      semver.ps.le_succ(p, q, h)

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
      %LLogicNat.semver.ps.eq_true(a, va, LLogicBool.semver.ps.and_l(Nat.is_eq(a, va), Nat.is_eq(b, vb), ins)) : {Bool.not(Sv.Ver.le3(a, _, b, vb, Sv.Rel.after(Sv.Rel.top(Sv.Ver{a, b, c}, List.append(&2, String, xs, t <> ys))), vc)) == True{} : Bool}
      %LLogicNat.semver.ps.eq_true(b, vb, LLogicBool.semver.ps.and_r(Nat.is_eq(a, va), Nat.is_eq(b, vb), ins)) : {Bool.not(Sv.Ver.le3(a, a, b, _, Sv.Rel.after(Sv.Rel.top(Sv.Ver{a, b, c}, List.append(&2, String, xs, t <> ys))), vc)) == True{} : Bool}
      %ps.le3_same(a, b, Sv.Rel.after(Sv.Rel.top(Sv.Ver{a, b, c}, List.append(&2, String, xs, t <> ys))), vc) : {Bool.not(_) == True{} : Bool}
      %Equal.sym(Bool, Sv.Num.le(Sv.Rel.after(Sv.Rel.top(Sv.Ver{a, b, c}, List.append(&2, String, xs, t <> ys))), vc), False{}, ps.after_gt(vc, Sv.Rel.top(Sv.Ver{a, b, c}, List.append(&2, String, xs, t <> ys)), ps.top_mid(Sv.Ver{a, b, c}, xs, t, ys, Sv.Ver{va, vb, vc}, parsed, ins))) : {Bool.not(_) == True{} : Bool}
      {==}

# the next release is of the series
def ps.series_next(s: Sv.Ver, tags: List<&2, String>) -> {Sv.Ver.in_series(s, Sv.Rel.next(s, tags)) == True{} : Bool}:
  match s:
    case Sv.Ver{+a, +b, c}:
      %LNat.semver.ps.eq_refl(a) : {Bool.and(_, Nat.is_eq(b, b)) == True{} : Bool}
      Equal.sym(Bool, True{}, Nat.is_eq(b, b), LNat.semver.ps.eq_refl(b))

def ps.next_ne.go(+s: Sv.Ver, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, +v: Sv.Ver, parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}, b: Bool, eb: {Sv.Ver.in_series(s, v) == b : Bool}, e: {v == Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)) : Sv.Ver}) -> Empty:
  match b:
    case True{}:
      ps.lt_ne(v, Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)), ps.next_newer(s, xs, t, ys, v, parsed, eb), e)
    case False{}:
      +same = Equal.cong(Sv.Ver, Bool, x => Sv.Ver.in_series(s, x), v, Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)), e)
      +into = Equal.trans(Bool, Sv.Ver.in_series(s, v), Sv.Ver.in_series(s, Sv.Rel.next(s, List.append(&2, String, xs, t <> ys))), True{}, same, ps.series_next(s, List.append(&2, String, xs, t <> ys)))
      LLogicLogic.semver.ps.absurdF(Empty, Equal.trans(Bool, False{}, Sv.Ver.in_series(s, v), True{}, Equal.sym(Bool, Sv.Ver.in_series(s, v), False{}, eb), into))

# no version tag names the next release
def ps.next_ne(+s: Sv.Ver, +xs: List<&2, String>, +t: String, +ys: List<&2, String>, +v: Sv.Ver, parsed: {Sv.Tag.ver(t) == Some{v} : Maybe<&2, Sv.Ver>}) -> {v != Sv.Rel.next(s, List.append(&2, String, xs, t <> ys)) : Sv.Ver}:
  e => ps.next_ne.go(s, xs, t, ys, v, parsed, Sv.Ver.in_series(s, v), {==}, e)

# a fresh series starts at patch 0
def ps.add_skip(+s: Sv.Ver, m: Maybe<&2, Sv.Ver>, +acc: Maybe<&2, Nat>, h: {Sv.Rel.ofs.of(s, m) == False{} : Bool}) -> {acc == Sv.Rel.add(s, m, acc) : Maybe<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{+w}:
      %Equal.sym(Bool, Sv.Ver.in_series(s, w), False{}, h) : {acc == Sv.Rel.keep(_, Sv.Ver.patch(w), acc) : Maybe<&2, Nat>}
      {==}
