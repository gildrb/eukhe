# eukhe: lemmas the proofs of area semver share

import Base
import ../../bend/ffi_semver.bend as FSv
import ../../bend/semver.bend as Sv
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/semver.bend as Semver
import ../../laws/wire.bend as Wire
import ../wire/wire_nat_exact.bend as PWireNatExact
import ../wire/wire_str_exact.bend as PWireStrExact
import ../base/wire.bend as LWire
import ./semver_show_decimal.bend as PSemverShowDecimal
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

# ---- entry ----

# The entry bend/ffi_semver.bend (laws/semver.bend section entry). A
# request is a tag, then strings and a list of strings: each reads back by
# the wire laws (wire_str_round_trip, and the list loop below), and each
# decoder layer that answers Got gives the prefix of the encoding
# (wire_nat_exact, wire_str_exact). The guard (no 7 digits in a row) is
# the spec's seven_spec, and each reply part is the spec's (sv_*).

# Lists of strings
# ----------------

# the items of a list of strings, then rest
def sv_ss_items(xs: List<&2, String>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case Con{x, t}:
      Wr.put_str(x, sv_ss_items(t, rest))

def sv_ss_put_go(xs: List<&2, String>, -rest: String) -> {Wr.put_list.go(~String, ~Wr.put_str, xs, rest) == (List.length(&2, String, xs), sv_ss_items(xs, rest)) : Nat & String}:
  match xs:
    case Nil{}:
      {==}
    case Con{x, +t}:
      %Equal.sym(Nat & String, Wr.put_list.go(~String, ~Wr.put_str, t, rest), (List.length(&2, String, t), sv_ss_items(t, rest)), sv_ss_put_go(t, rest)) : {Wr.put_list.step(~String, ~Wr.put_str, x, _) == (1n+List.length(&2, String, t), Wr.put_str(x, sv_ss_items(t, rest))) : Nat & String}
      {==}

# a list of strings is its count, then its items
def sv_ss_put(+xs: List<&2, String>, -rest: String) -> {Wr.put_list(~String, ~Wr.put_str, xs, rest) == Wr.put_nat(List.length(&2, String, xs), sv_ss_items(xs, rest)) : String}:
  %Equal.sym(Nat & String, Wr.put_list.go(~String, ~Wr.put_str, xs, rest), (List.length(&2, String, xs), sv_ss_items(xs, rest)), sv_ss_put_go(xs, rest)) : {Wr.put_list.fin(_) == Wr.put_nat(List.length(&2, String, xs), sv_ss_items(xs, rest)) : String}
  {==}

# the item loop reads back x then t
def sv_ss_go_rt(+t: List<&2, String>, +x: String, +rest: String, +hf: {Semver.strs_all(x <> t) == True{} : Bool}) -> {Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, t), Wr.get_str(Wr.put_str(x, sv_ss_items(t, rest)))) == Wr.Got{x <> t, rest} : Wr.Dec<List<&2, String>>}:
  match t:
    case Nil{}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(x)), True{}, hf))) : {Wr.get_list.go(~String, ~Wr.get_str, 0n, _) == Wr.Got{[x], rest} : Wr.Dec<List<&2, String>>}
      {==}
    case Con{+y, +u}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, Wr.put_str(y, sv_ss_items(u, rest)))), Wr.Got{x, Wr.put_str(y, sv_ss_items(u, rest))}, Wire.wire_str_round_trip(x, Wr.put_str(y, sv_ss_items(u, rest)), LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(x)), Semver.strs_all(y <> u), hf))) : {Wr.get_list.go(~String, ~Wr.get_str, 1n+List.length(&2, String, u), _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, String>>}
      %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list.go(~String, ~Wr.get_str, List.length(&2, String, u), Wr.get_str(Wr.put_str(y, sv_ss_items(u, rest)))), Wr.Got{y <> u, rest}, sv_ss_go_rt(u, y, rest, LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(x)), Semver.strs_all(y <> u), hf))) : {Wr.get_list.cons(String, x, _) == Wr.Got{x <> y <> u, rest} : Wr.Dec<List<&2, String>>}
      {==}

# a list of strings that fits reads back
def sv_tags_rt(+xs: List<&2, String>, +rest: String, h: {Bool.and(LawsBase.wire_fits(List.length(&2, String, xs)), Semver.strs_all(xs)) == True{} : Bool}) -> {Wr.get_list(~String, ~Wr.get_str, Semver.spell_tags(xs, rest)) == Wr.Got{xs, rest} : Wr.Dec<List<&2, String>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, +t}:
      +r = rest
      +hh = h
      %Equal.sym(String, Wr.put_list(~String, ~Wr.put_str, x <> t, r), Wr.put_nat(List.length(&2, String, x <> t), sv_ss_items(x <> t, r)), sv_ss_put(x <> t, r)) : {Wr.get_list(~String, ~Wr.get_str, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, String>>}
      %Equal.sym(Wr.Dec<Nat>, Wr.get_nat(Wr.put_nat(List.length(&2, String, x <> t), sv_ss_items(x <> t, r))), Wr.Got{List.length(&2, String, x <> t), sv_ss_items(x <> t, r)}, Wire.wire_nat_round_trip(List.length(&2, String, x <> t), sv_ss_items(x <> t, r), LLogicBool.wr_and_l(LawsBase.wire_fits(List.length(&2, String, x <> t)), Semver.strs_all(x <> t), hh))) : {Wr.get_list.start(~String, ~Wr.get_str, _) == Wr.Got{x <> t, r} : Wr.Dec<List<&2, String>>}
      sv_ss_go_rt(t, x, r, LLogicBool.wr_and_r(LawsBase.wire_fits(List.length(&2, String, x <> t)), Semver.strs_all(x <> t), hh))

# Requests read back
# ------------------

def sv_dec_release(+c: String, +ts: List<&2, String>, +h: {Semver.release_fits(c, ts) == True{} : Bool}) -> {FSv.get_req(Semver.spell_release(c, ts)) == Wr.Got{FSv.QRelease{c, ts}, ""} : Wr.Dec<FSv.Req>}:
  +hc = LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(c)), Bool.and(LawsBase.wire_fits(List.length(&2, String, ts)), Semver.strs_all(ts)), h)
  +ht = LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(c)), Bool.and(LawsBase.wire_fits(List.length(&2, String, ts)), Semver.strs_all(ts)), h)
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(c, Semver.spell_tags(ts, ""))), Wr.Got{c, Semver.spell_tags(ts, "")}, Wire.wire_str_round_trip(c, Semver.spell_tags(ts, ""), hc)) : {FSv.get_release(_) == Wr.Got{FSv.QRelease{c, ts}, ""} : Wr.Dec<FSv.Req>}
  %Equal.sym(Wr.Dec<List<&2, String>>, Wr.get_list(~String, ~Wr.get_str, Semver.spell_tags(ts, "")), Wr.Got{ts, ""}, sv_tags_rt(ts, "", ht)) : {FSv.get_release.tags(c, _) == Wr.Got{FSv.QRelease{c, ts}, ""} : Wr.Dec<FSv.Req>}
  {==}

def sv_dec_series(+w: String, +r: String, +h: {Semver.series_fits(w, r) == True{} : Bool}) -> {FSv.get_req(Semver.spell_series(w, r)) == Wr.Got{FSv.QSeries{w, r}, ""} : Wr.Dec<FSv.Req>}:
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(w, Wr.put_str(r, ""))), Wr.Got{w, Wr.put_str(r, "")}, Wire.wire_str_round_trip(w, Wr.put_str(r, ""), LLogicBool.wr_and_l(LawsBase.wire_fits(String.length(w)), LawsBase.wire_fits(String.length(r)), h))) : {FSv.get_series(_) == Wr.Got{FSv.QSeries{w, r}, ""} : Wr.Dec<FSv.Req>}
  %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(r, "")), Wr.Got{r, ""}, Wire.wire_str_round_trip(r, "", LLogicBool.wr_and_r(LawsBase.wire_fits(String.length(w)), LawsBase.wire_fits(String.length(r)), h))) : {FSv.get_series.release(w, _) == Wr.Got{FSv.QSeries{w, r}, ""} : Wr.Dec<FSv.Req>}
  {==}

# The guard is the spec's
# -----------------------

def sv_digit(y: Sv.Sym) -> {FSv.digit.of(y) == Semver.digit_spec.of(y) : Bool}:
  match y:
    case Sv.Digit{d}:
      {==}
    case Sv.Dot{}:
      {==}
    case Sv.Other{}:
      {==}

def sv_lead(n: Nat, s: String) -> {FSv.lead(n, s) == Semver.run_spec(n, s) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      match s:
        case SNil{}:
          {==}
        case SCon{c, +t}:
          %sv_lead(m, t) : {FSv.lead(1n+m, SCon{c, t}) == Bool.and(Semver.digit_spec.of(Sv.Sym.of(c)), _) : Bool}
          %sv_digit(Sv.Sym.of(c)) : {Bool.and(FSv.digit(c), FSv.lead(m, t)) == Bool.and(_, FSv.lead(m, t)) : Bool}
          {==}

def sv_long(s: String) -> {FSv.long(s) == Semver.seven_spec(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %sv_long(t) : {Bool.or(FSv.lead(7n, SCon{c, t}), FSv.long(t)) == Bool.or(Semver.run_spec(7n, SCon{c, t}), _) : Bool}
      %sv_lead(7n, SCon{c, t}) : {Bool.or(FSv.lead(7n, SCon{c, t}), FSv.long(t)) == Bool.or(_, FSv.long(t)) : Bool}
      {==}

# not a and not b is not (a or b)
def sv_dm(a: Bool, -b: Bool) -> {Bool.and(Bool.not(a), Bool.not(b)) == Bool.not(Bool.or(a, b)) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def sv_short(+s: String) -> {FSv.short(s) == Bool.not(Semver.seven_spec(s)) : Bool}:
  %sv_long(s) : {Bool.not(FSv.long(s)) == Bool.not(_) : Bool}
  {==}

def sv_short_tag.of(m: Maybe<&2, String>) -> {FSv.short.tag.of(m) == Bool.not(Semver.seven_tag.of(m)) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+r}:
      sv_short(r)

def sv_short_tags(ts: List<&2, String>) -> {FSv.short.tags(ts) == Bool.not(Semver.seven_tags(ts)) : Bool}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +r:
      %Equal.sym(Bool, FSv.short.tags(r), Bool.not(Semver.seven_tags(r)), sv_short_tags(r)) : {Bool.and(FSv.short.tag(t), _) == Bool.not(Bool.or(Semver.seven_tag(t), Semver.seven_tags(r))) : Bool}
      %Equal.sym(Bool, FSv.short.tag.of(Sv.Tag.strip(t)), Bool.not(Semver.seven_tag.of(Sv.Tag.strip(t))), sv_short_tag.of(Sv.Tag.strip(t))) : {Bool.and(_, Bool.not(Semver.seven_tags(r))) == Bool.not(Bool.or(Semver.seven_tag(t), Semver.seven_tags(r))) : Bool}
      sv_dm(Semver.seven_tag(t), Semver.seven_tags(r))

def sv_req_release(+c: String, +ts: List<&2, String>) -> {FSv.short.req(FSv.QRelease{c, ts}) == Bool.not(Bool.or(Semver.seven_spec(c), Semver.seven_tags(ts))) : Bool}:
  %Equal.sym(Bool, FSv.short.tags(ts), Bool.not(Semver.seven_tags(ts)), sv_short_tags(ts)) : {Bool.and(FSv.short(c), _) == Bool.not(Bool.or(Semver.seven_spec(c), Semver.seven_tags(ts))) : Bool}
  %Equal.sym(Bool, FSv.short(c), Bool.not(Semver.seven_spec(c)), sv_short(c)) : {Bool.and(_, Bool.not(Semver.seven_tags(ts))) == Bool.not(Bool.or(Semver.seven_spec(c), Semver.seven_tags(ts))) : Bool}
  sv_dm(Semver.seven_spec(c), Semver.seven_tags(ts))

def sv_req_series(+w: String, +r: String) -> {FSv.short.req(FSv.QSeries{w, r}) == Bool.not(Bool.or(Semver.seven_spec(w), Semver.seven_spec(r))) : Bool}:
  %Equal.sym(Bool, FSv.short(r), Bool.not(Semver.seven_spec(r)), sv_short(r)) : {Bool.and(FSv.short(w), _) == Bool.not(Bool.or(Semver.seven_spec(w), Semver.seven_spec(r))) : Bool}
  %Equal.sym(Bool, FSv.short(w), Bool.not(Semver.seven_spec(w)), sv_short(w)) : {Bool.and(_, Bool.not(Semver.seven_spec(r))) == Bool.not(Bool.or(Semver.seven_spec(w), Semver.seven_spec(r))) : Bool}
  sv_dm(Semver.seven_spec(w), Semver.seven_spec(r))

# a guard that is not of a False/True premise
def sv_not_false(-a: Bool, -x: Bool, e: {a == Bool.not(x) : Bool}, h: {x == False{} : Bool}) -> {a == True{} : Bool}:
  %h : {a == Bool.not(_) : Bool}
  e

def sv_not_true(-a: Bool, -x: Bool, e: {a == Bool.not(x) : Bool}, h: {x == True{} : Bool}) -> {a == False{} : Bool}:
  %h : {a == Bool.not(_) : Bool}
  e

# The replies are the spec's
# --------------------------

def sv_keep_not(b: Bool, -t: String, -rest: List<&2, String>) -> {FSv.newer.keep(Bool.not(b), t, rest) == Semver.newer_spec.pick(b, t, rest) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sv_newer_keep(m: Maybe<&2, Sv.Ver>, +n: Sv.Ver, -t: String, -rest: List<&2, String>) -> {FSv.newer.keep(Sv.Rel.older(n, m), t, rest) == Semver.newer_spec.keep(m, n, t, rest) : List<&2, String>}:
  match m:
    case None{}:
      {==}
    case Some{+v}:
      sv_keep_not(Sv.Ver.le(n, v), t, rest)

def sv_newer(+n: Sv.Ver, ts: List<&2, String>) -> {FSv.newer(n, ts) == Semver.newer_spec(n, ts) : List<&2, String>}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +r:
      %sv_newer(n, r) : {FSv.newer(n, t <> r) == Semver.newer_spec.keep(Sv.Tag.ver(t), n, t, _) : List<&2, String>}
      sv_newer_keep(Sv.Tag.ver(t), n, t, FSv.newer(n, r))

def sv_show(v: Sv.Ver) -> {Sv.Ver.show(v) == Semver.show_spec(v) : String}:
  match v:
    case Sv.Ver{a, b, c}:
      Semver.semver_show_decimal(a, b, c)

def sv_put_rel(+v: Sv.Ver) -> {Wr.put_nat(3n, FSv.put_rel(v, "")) == Semver.spell_rel(v) : String}:
  %sv_show(v) : {Wr.put_nat(3n, FSv.put_rel(v, "")) == Wr.put_nat(3n, Wr.put_str(_, Wr.put_str(String.append("eukhe-v", _), Wr.put_str(String.append("Eukhe v", _), "")))) : String}
  {==}

def sv_patch(+a: Nat, +b: Nat, c: Nat, +ts: List<&2, String>) -> {FSv.release.patch(a, b, c, ts) == Semver.why_spec.patch(a, b, c, ts) : String}:
  match c:
    case 0n:
      +n = Sv.Rel.next(Sv.Ver{a, b, 0n}, ts)
      %sv_newer(n, ts) : {FSv.release.patch(a, b, 0n, ts) == Wr.put_nat(2n, Wr.put_str(Semver.show_spec(n), Semver.spell_tags(_, ""))) : String}
      %sv_show(n) : {FSv.release.patch(a, b, 0n, ts) == Wr.put_nat(2n, Wr.put_str(_, Semver.spell_tags(FSv.newer(n, ts), ""))) : String}
      {==}
    case 1n+z:
      {==}

def sv_miss(m: Maybe<&2, Sv.Ver>, +ts: List<&2, String>) -> {FSv.release.miss(m, ts) == Semver.why_spec(m, ts) : String}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case Sv.Ver{+a, +b, c}:
          sv_patch(a, b, c, ts)

def sv_put(r: Maybe<&2, Sv.Ver>, +c: String, +ts: List<&2, String>) -> {FSv.release.put(r, c, ts) == Semver.release_spec.of(r, c, ts) : String}:
  match r:
    case Some{+v}:
      sv_put_rel(v)
    case None{}:
      sv_miss(Sv.Ver.parse(c), ts)

def sv_series_in(b: Bool) -> {Wr.put_nat(FSv.series.in(b), "") == Semver.series_spec.in(b) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sv_series(r: Maybe<&2, Sv.Ver>, w: Maybe<&2, Sv.Ver>) -> {Wr.put_nat(FSv.series.of(r, w), "") == Semver.series_spec.of(r, w) : String}:
  match r:
    case None{}:
      {==}
    case Some{v}:
      match w:
        case None{}:
          {==}
        case Some{s}:
          sv_series_in(Sv.Ver.in_series(s, v))

# Exactness
# ---------

# what the item loop's answer says about its input s (m + 1 items)
def sv_pl(s: String, m: Nat, d: Wr.Dec<List<&2, String>>) -> Type:
  match d:
    case Wr.Got{+xs, r}:
      {s == sv_ss_items(xs, r) : String} & {List.length(&2, String, xs) == 1n+m : Nat}
    case Wr.Bad{}:
      Unit

def sv_list_step(-s: String, +x: String, +s3: String, -k: Nat, ex: {s == Wr.put_str(x, s3) : String},
  d: Wr.Dec<List<&2, String>>, ih: sv_pl(s3, k, d)) -> sv_pl(s, 1n+k, Wr.get_list.cons(String, x, d)):
  match d:
    case Wr.Got{+ys, +r}:
      (e1, e2) = ih
      (Equal.trans(String, s, Wr.put_str(x, s3), Wr.put_str(x, sv_ss_items(ys, r)), ex,
          Equal.cong(String, String, z => Wr.put_str(x, z), s3, sv_ss_items(ys, r), e1)),
        Equal.cong(Nat, Nat, k2 => 1n+k2, List.length(&2, String, ys), 1n+k, e2))
    case Wr.Bad{}:
      Unit{}

# the item loop accepts only items that are encodings
def sv_list_spec(m: Nat, cur: Wr.Dec<String>, +s: String, er: {Wr.get_str(s) == cur : Wr.Dec<String>}) ->
  sv_pl(s, m, Wr.get_list.go(~String, ~Wr.get_str, m, cur)):
  match m cur:
    case 0n Wr.Got{+x, +s3}:
      (Wire.wire_str_exact(s, x, s3, er), {==})
    case 0n Wr.Bad{}:
      Unit{}
    case 1n++k Wr.Got{+x, +s3}:
      sv_list_step(s, x, s3, k, Wire.wire_str_exact(s, x, s3, er),
        Wr.get_list.go(~String, ~Wr.get_str, k, Wr.get_str(s3)), sv_list_spec(k, Wr.get_str(s3), s3, {==}))
    case 1n++k Wr.Bad{}:
      Unit{}

# what a list decoder answer says about its input s
def sv_pls(s: String, d: Wr.Dec<List<&2, String>>) -> Type:
  match d:
    case Wr.Got{xs, r}:
      {s == Wr.put_list(~String, ~Wr.put_str, xs, r) : String}
    case Wr.Bad{}:
      Unit

def sv_list_conv(+s: String, +s2: String, -m: Nat, en: {s == Wr.put_nat(1n+m, s2) : String},
  d: Wr.Dec<List<&2, String>>, pl: sv_pl(s2, m, d)) -> sv_pls(s, d):
  match d:
    case Wr.Got{+xs, +r}:
      (e1, e2) = pl
      %Equal.sym(String, Wr.put_list(~String, ~Wr.put_str, xs, r), Wr.put_nat(List.length(&2, String, xs), sv_ss_items(xs, r)), sv_ss_put(xs, r)) : {s == _ : String}
      %Equal.sym(Nat, List.length(&2, String, xs), 1n+m, e2) : {s == Wr.put_nat(_, sv_ss_items(xs, r)) : String}
      %e1 : {s == Wr.put_nat(1n+m, _) : String}
      en
    case Wr.Bad{}:
      Unit{}

def sv_list_nat(+s: String, n: Nat, +s2: String, en: {s == Wr.put_nat(n, s2) : String}) ->
  sv_pls(s, Wr.get_list.start(~String, ~Wr.get_str, Wr.Got{n, s2})):
  match n:
    case 0n:
      en
    case 1n++m:
      sv_list_conv(s, s2, m, en, Wr.get_list.go(~String, ~Wr.get_str, m, Wr.get_str(s2)),
        sv_list_spec(m, Wr.get_str(s2), s2, {==}))

def sv_list_top(+s: String, r: Wr.Dec<Nat>, er: {Wr.get_nat(s) == r : Wr.Dec<Nat>}) ->
  sv_pls(s, Wr.get_list.start(~String, ~Wr.get_str, r)):
  match r:
    case Wr.Got{+n, +s2}:
      sv_list_nat(s, n, s2, Wire.wire_nat_exact(s, n, s2, er))
    case Wr.Bad{}:
      Unit{}

# a decoded list of strings is exactly its encoding
def sv_tags_ex(+s: String, -xs: List<&2, String>, -rest: String, h: {Wr.get_list(~String, ~Wr.get_str, s) == Wr.Got{xs, rest} : Wr.Dec<List<&2, String>>}) -> {s == Semver.spell_tags(xs, rest) : String}:
  %h : sv_pls(s, _)
  sv_list_top(s, Wr.get_nat(s), {==})

# The witness
# -----------

def sv_ex_rel(-s: String, -c: String, -s2: String, -ts: List<&2, String>, e2: {s2 == Semver.spell_tags(ts, "") : String}, es: {s == Wr.put_nat(0n, Wr.put_str(c, s2)) : String}) -> {s == Semver.spell_release(c, ts) : String}:
  %e2 : {s == Wr.put_nat(0n, Wr.put_str(c, _)) : String}
  es

def sv_ex_tags(+s: String, +c: String, +s2: String, d: Wr.Dec<List<&2, String>>, ed: {Wr.get_list(~String, ~Wr.get_str, s2) == d : Wr.Dec<List<&2, String>>}, es: {s == Wr.put_nat(0n, Wr.put_str(c, s2)) : String}, ok: {LawsBase.wire_opens_err(FSv.ffi.got(FSv.get_release.tags(c, d))) == False{} : Bool}) -> Sigma<&1, &1, FSv.Req, q => {s == Semver.spell_req(q) : String}>:
  match d:
    case Wr.Got{+ts, s3}:
      match s3:
        case SNil{}:
          (FSv.QRelease{c, ts}, sv_ex_rel(s, c, s2, ts, sv_tags_ex(s2, ts, "", ed), es))
        case SCon{x, y}:
          LLogicLogic.semver.ps.absurd(Sigma<&1, &1, FSv.Req, q => {s == Semver.spell_req(q) : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.semver.ps.absurd(Sigma<&1, &1, FSv.Req, q => {s == Semver.spell_req(q) : String}>, ok)

# s is the tag t, then s1, and s1 is x
def sv_ex_sub(-s: String, -s1: String, -x: String, e1: {s1 == x : String}, es: {s == Wr.put_nat(0n, s1) : String}) -> {s == Wr.put_nat(0n, x) : String}:
  %e1 : {s == Wr.put_nat(0n, _) : String}
  es

def sv_ex_sub1(-s: String, -s1: String, -x: String, e1: {s1 == x : String}, es: {s == Wr.put_nat(1n, s1) : String}) -> {s == Wr.put_nat(1n, x) : String}:
  %e1 : {s == Wr.put_nat(1n, _) : String}
  es

def sv_ex_ser(-s: String, -w: String, -s2: String, -r: String, e2: {s2 == Wr.put_str(r, "") : String}, es: {s == Wr.put_nat(1n, Wr.put_str(w, s2)) : String}) -> {s == Semver.spell_series(w, r) : String}:
  %e2 : {s == Wr.put_nat(1n, Wr.put_str(w, _)) : String}
  es

def sv_ex_rel_str(+s: String, +s1: String, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}, es: {s == Wr.put_nat(0n, s1) : String}, ok: {LawsBase.wire_opens_err(FSv.ffi.got(FSv.get_release(d))) == False{} : Bool}) -> Sigma<&1, &1, FSv.Req, q => {s == Semver.spell_req(q) : String}>:
  match d:
    case Wr.Got{+c, +s2}:
      +e1 = Wire.wire_str_exact(s1, c, s2, ed)
      sv_ex_tags(s, c, s2, Wr.get_list(~String, ~Wr.get_str, s2), {==}, sv_ex_sub(s, s1, Wr.put_str(c, s2), e1, es), ok)
    case Wr.Bad{}:
      LLogicLogic.semver.ps.absurd(Sigma<&1, &1, FSv.Req, q => {s == Semver.spell_req(q) : String}>, ok)

def sv_ex_ser_rel(+s: String, +w: String, +s2: String, d: Wr.Dec<String>, ed: {Wr.get_str(s2) == d : Wr.Dec<String>}, es: {s == Wr.put_nat(1n, Wr.put_str(w, s2)) : String}, ok: {LawsBase.wire_opens_err(FSv.ffi.got(FSv.get_series.release(w, d))) == False{} : Bool}) -> Sigma<&1, &1, FSv.Req, q => {s == Semver.spell_req(q) : String}>:
  match d:
    case Wr.Got{+r, s3}:
      match s3:
        case SNil{}:
          (FSv.QSeries{w, r}, sv_ex_ser(s, w, s2, r, Wire.wire_str_exact(s2, r, "", ed), es))
        case SCon{x, y}:
          LLogicLogic.semver.ps.absurd(Sigma<&1, &1, FSv.Req, q => {s == Semver.spell_req(q) : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.semver.ps.absurd(Sigma<&1, &1, FSv.Req, q => {s == Semver.spell_req(q) : String}>, ok)

def sv_ex_ser_str(+s: String, +s1: String, d: Wr.Dec<String>, ed: {Wr.get_str(s1) == d : Wr.Dec<String>}, es: {s == Wr.put_nat(1n, s1) : String}, ok: {LawsBase.wire_opens_err(FSv.ffi.got(FSv.get_series(d))) == False{} : Bool}) -> Sigma<&1, &1, FSv.Req, q => {s == Semver.spell_req(q) : String}>:
  match d:
    case Wr.Got{+w, +s2}:
      sv_ex_ser_rel(s, w, s2, Wr.get_str(s2), {==}, sv_ex_sub1(s, s1, Wr.put_str(w, s2), Wire.wire_str_exact(s1, w, s2, ed), es), ok)
    case Wr.Bad{}:
      LLogicLogic.semver.ps.absurd(Sigma<&1, &1, FSv.Req, q => {s == Semver.spell_req(q) : String}>, ok)

# a reply that is no error comes from a spelled request
def sv_ex_top(+s: String, d: Wr.Dec<Nat>, ed: {Wr.get_nat(s) == d : Wr.Dec<Nat>}, ok: {LawsBase.wire_opens_err(FSv.ffi.got(FSv.get_req.start(d))) == False{} : Bool}) -> Sigma<&1, &1, FSv.Req, q => {s == Semver.spell_req(q) : String}>:
  match d:
    case Wr.Got{+t, +s1}:
      match t:
        case 0n:
          sv_ex_rel_str(s, s1, Wr.get_str(s1), {==}, Wire.wire_nat_exact(s, 0n, s1, ed), ok)
        case 1n:
          sv_ex_ser_str(s, s1, Wr.get_str(s1), {==}, Wire.wire_nat_exact(s, 1n, s1, ed), ok)
        case 2n+u:
          LLogicLogic.semver.ps.absurd(Sigma<&1, &1, FSv.Req, q => {s == Semver.spell_req(q) : String}>, ok)
    case Wr.Bad{}:
      LLogicLogic.semver.ps.absurd(Sigma<&1, &1, FSv.Req, q => {s == Semver.spell_req(q) : String}>, ok)
