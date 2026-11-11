# eukhe: lemmas the proofs of area theme_pick share: the theme a pick
# resolves to is the resolution over the candidates; a source's candidates
# skip the files that do not offer the name and find the first that does;
# the builtins answer by their names; the cause is the first file that
# blames the name.

import Base
import ../../bend/theme/choice.bend as TChoice
import ../../bend/theme/name.bend as TName
import ../../laws/theme_pick.bend as ThemePick
import ../theme/base.bend as LA

# Nat and lists
# -------------

def pk.add0(k: Nat) -> {k == Nat.add(k, 0n) : Nat}:
  match k:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, p, Nat.add(p, 0n), pk.add0(p))

def pk.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, x => 1n+x, Nat.add(p, 1n+b), 1n+Nat.add(p, b), pk.add_succ(p, b))

def pk.app_nil(xs: List<&2, TName.Cand>) -> {xs == List.append(&2, TName.Cand, xs, Nil{}) : List<&2, TName.Cand>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+x, rest}:
      Equal.cong(List<&2, TName.Cand>, List<&2, TName.Cand>, ys => x <> ys, rest, List.append(&2, TName.Cand, rest, Nil{}), pk.app_nil(rest))

def pk.not_t(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {b == False{} : Bool}:
  match b:
    case True{}:
      Equal.sym(Bool, False{}, True{}, h)
    case False{}:
      {==}

# The pick's theme
# ----------------

# the pick reports the resolution it is built on
def pk.res(r: TName.Res, +ls: List<&2, TChoice.Ld>, +n: String) -> {ThemePick.th.res(TChoice.pick.go(r, ls, n)) == r : TName.Res}:
  match r:
    case TName.Res{id, w}:
      match w:
        case True{}:
          {==}
        case False{}:
          {==}

def pk.res_pick(+ls: List<&2, TChoice.Ld>, +n: String) -> {ThemePick.th.res(TChoice.pick(ls, n)) == TChoice.pick.res(ls, n) : TName.Res}:
  pk.res(TChoice.pick.res(ls, n), ls, n)

# a name that is not empty resolves by the search
def pk.nonempty(+src: List<&2, TName.Cand>, +n: String, ne: {String.is_empty(n) == False{} : Bool}) -> {TName.resolve.name(src, n) == TName.find(src, n) : TName.Res}:
  %Equal.sym(Bool, String.is_empty(n), False{}, ne) : {TName.resolve.name.pick(_, src, n) == TName.find(src, n) : TName.Res}
  {==}

# A source's files
# ----------------

# the file l offers n from the source c0 (custom when True)
def pk.off(l: TChoice.Ld, +n: String, +c0: Bool) -> Bool:
  match l:
    case TChoice.Fine{m, c}:
      Bool.and(TChoice.same(c, c0), String.eq(m, n))
    case TChoice.Broke{nm, st}:
      False{}

def pk.none(ls: List<&2, TChoice.Ld>, +n: String, +c0: Bool) -> Bool:
  match ls:
    case Nil{}:
      True{}
    case Con{l, rest}:
      Bool.and(Bool.not(pk.off(l, n, c0)), pk.none(rest, n, c0))

def pk.off_reg(l: TChoice.Ld, +n: String) -> {ThemePick.th.offers.reg(l, n) == pk.off(l, n, False{}) : Bool}:
  match l:
    case TChoice.Fine{m, c}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}
    case TChoice.Broke{nm, st}:
      {==}

def pk.off_custom(l: TChoice.Ld, +n: String) -> {ThemePick.th.offers.custom(l, n) == pk.off(l, n, True{}) : Bool}:
  match l:
    case TChoice.Fine{m, c}:
      match c:
        case True{}:
          {==}
        case False{}:
          {==}
    case TChoice.Broke{nm, st}:
      {==}

def pk.none_reg(ls: List<&2, TChoice.Ld>, +n: String) -> {ThemePick.th.none.reg(ls, n) == pk.none(ls, n, False{}) : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, rest}:
      %Equal.sym(Bool, ThemePick.th.offers.reg(l, n), pk.off(l, n, False{}), pk.off_reg(l, n)) : {Bool.and(Bool.not(_), ThemePick.th.none.reg(rest, n)) == Bool.and(Bool.not(pk.off(l, n, False{})), pk.none(rest, n, False{})) : Bool}
      %Equal.sym(Bool, ThemePick.th.none.reg(rest, n), pk.none(rest, n, False{}), pk.none_reg(rest, n)) : {Bool.and(Bool.not(pk.off(l, n, False{})), _) == Bool.and(Bool.not(pk.off(l, n, False{})), pk.none(rest, n, False{})) : Bool}
      {==}

def pk.none_custom(ls: List<&2, TChoice.Ld>, +n: String) -> {ThemePick.th.none.custom(ls, n) == pk.none(ls, n, True{}) : Bool}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, rest}:
      %Equal.sym(Bool, ThemePick.th.offers.custom(l, n), pk.off(l, n, True{}), pk.off_custom(l, n)) : {Bool.and(Bool.not(_), ThemePick.th.none.custom(rest, n)) == Bool.and(Bool.not(pk.off(l, n, True{})), pk.none(rest, n, True{})) : Bool}
      %Equal.sym(Bool, ThemePick.th.none.custom(rest, n), pk.none(rest, n, True{}), pk.none_custom(rest, n)) : {Bool.and(Bool.not(pk.off(l, n, True{})), _) == Bool.and(Bool.not(pk.off(l, n, True{})), pk.none(rest, n, True{})) : Bool}
      {==}

# a candidate that does not resolve n is passed over
def pk.pass(+nm: String, +id: U32, -rest: List<&2, TName.Cand>, +n: String, -x: TName.Res, he: {String.eq(nm, n) == False{} : Bool}, ih: {TName.find(rest, n) == x : TName.Res}) -> {TName.find(TName.Cand{nm, True{}, id} <> rest, n) == x : TName.Res}:
  %Equal.sym(Bool, String.eq(nm, n), False{}, he) : {TName.find.pick(Bool.and(True{}, _), id, TName.find(rest, n)) == x : TName.Res}
  ih

# one file of a source that does not offer n changes nothing the search
# finds after it
def pk.step(l: TChoice.Ld, +c0: Bool, +at: Nat, -rc: List<&2, TName.Cand>, -r: List<&2, TName.Cand>, +n: String, -x: TName.Res, ho: {Bool.not(pk.off(l, n, c0)) == True{} : Bool}, ih: {TName.find(List.append(&2, TName.Cand, rc, r), n) == x : TName.Res})
  -> {TName.find(List.append(&2, TName.Cand, TChoice.cands.of(l, c0, at, rc), r), n) == x : TName.Res}:
  match l:
    case TChoice.Fine{+m, c}:
      match c c0:
        case True{} True{}:
          pk.pass(m, TChoice.file.id(at), List.append(&2, TName.Cand, rc, r), n, x, pk.not_t(String.eq(m, n), ho), ih)
        case True{} False{}:
          ih
        case False{} True{}:
          ih
        case False{} False{}:
          pk.pass(m, TChoice.file.id(at), List.append(&2, TName.Cand, rc, r), n, x, pk.not_t(String.eq(m, n), ho), ih)
    case TChoice.Broke{nm, st}:
      ih

# the files of a source none of which offers n are passed over
def pk.skip(ls: List<&2, TChoice.Ld>, +c0: Bool, +at: Nat, +r: List<&2, TName.Cand>, +n: String, +no: {pk.none(ls, n, c0) == True{} : Bool})
  -> {TName.find(List.append(&2, TName.Cand, TChoice.cands(ls, c0, at), r), n) == TName.find(r, n) : TName.Res}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +rest}:
      +ho = LA.themes.pt.and_l(Bool.not(pk.off(l, n, c0)), pk.none(rest, n, c0), no)
      +ih = pk.skip(rest, c0, 1n+at, r, n, LA.themes.pt.and_r(Bool.not(pk.off(l, n, c0)), pk.none(rest, n, c0), no))
      pk.step(l, c0, at, TChoice.cands(rest, c0, 1n+at), r, n, TName.find(r, n), ho, ih)

def pk.hit(+nm: String, +c0: Bool, +at: Nat, -rc: List<&2, TName.Cand>, -r: List<&2, TName.Cand>, +n: String, same: {String.eq(nm, n) == True{} : Bool})
  -> {TName.find(List.append(&2, TName.Cand, TChoice.cands.of(TChoice.Fine{nm, c0}, c0, at, rc), r), n) == TName.Res{TChoice.file.id(at), False{}} : TName.Res}:
  match c0:
    case True{}:
      %Equal.sym(Bool, String.eq(nm, n), True{}, same) : {TName.find.pick(Bool.and(True{}, _), TChoice.file.id(at), TName.find(List.append(&2, TName.Cand, rc, r), n)) == TName.Res{TChoice.file.id(at), False{}} : TName.Res}
      {==}
    case False{}:
      %Equal.sym(Bool, String.eq(nm, n), True{}, same) : {TName.find.pick(Bool.and(True{}, _), TChoice.file.id(at), TName.find(List.append(&2, TName.Cand, rc, r), n)) == TName.Res{TChoice.file.id(at), False{}} : TName.Res}
      {==}

# the first file of a source that offers n is found, by its index
def pk.found(pre: List<&2, TChoice.Ld>, +nm: String, +post: List<&2, TChoice.Ld>, +c0: Bool, +at: Nat, +r: List<&2, TName.Cand>, +n: String, +no: {pk.none(pre, n, c0) == True{} : Bool}, same: {String.eq(nm, n) == True{} : Bool})
  -> {TName.find(List.append(&2, TName.Cand, TChoice.cands(List.append(&2, TChoice.Ld, pre, TChoice.Fine{nm, c0} <> post), c0, at), r), n) == TName.Res{TChoice.file.id(Nat.add(List.length(&2, TChoice.Ld, pre), at)), False{}} : TName.Res}:
  match pre:
    case Nil{}:
      pk.hit(nm, c0, at, TChoice.cands(post, c0, 1n+at), r, n, same)
    case Con{+l, +rest}:
      +ho = LA.themes.pt.and_l(Bool.not(pk.off(l, n, c0)), pk.none(rest, n, c0), no)
      +ih = pk.found(rest, nm, post, c0, 1n+at, r, n, LA.themes.pt.and_r(Bool.not(pk.off(l, n, c0)), pk.none(rest, n, c0), no), same)
      %pk.add_succ(List.length(&2, TChoice.Ld, rest), at) : {TName.find(List.append(&2, TName.Cand, TChoice.cands(List.append(&2, TChoice.Ld, l <> rest, TChoice.Fine{nm, c0} <> post), c0, at), r), n) == TName.Res{TChoice.file.id(_), False{}} : TName.Res}
      pk.step(l, c0, at, TChoice.cands(List.append(&2, TChoice.Ld, rest, TChoice.Fine{nm, c0} <> post), c0, 1n+at), r, n, TName.Res{TChoice.file.id(Nat.add(List.length(&2, TChoice.Ld, rest), 1n+at)), False{}}, ho, ih)

# The builtins
# ------------

def pk.some_eq(-a: Nat, -k: Nat, h: {Some{a} == Some{k} : Maybe<&2, Nat>}) -> {a == k : Nat}:
  Equal.cong(Maybe<&2, Nat>, Nat, m => Maybe.default(&2, Nat, m, 0n), Some{a}, Some{k}, h)

def pk.res_at(+a: Nat, +k: Nat, h: {Some{a} == Some{k} : Maybe<&2, Nat>}) -> {TName.Res{U32.from_nat(a), False{}} == TName.Res{U32.from_nat(k), False{}} : TName.Res}:
  Equal.cong(Nat, TName.Res, x => TName.Res{U32.from_nat(x), False{}}, a, k, pk.some_eq(a, k, h))

def pk.some_none(-A: Data, -a: A, -G: Type, h: {Some{a} == None{} : Maybe<&2, A>}) -> G:
  LA.pt.none_some(A, a, G, Equal.sym(Maybe<&2, A>, Some{a}, None{}, h))

# a name of a builtin finds it, by its index
def pk.bi(b1: Bool, b2: Bool, b3: Bool, -r: List<&2, TName.Cand>, +n: String, +k: Nat, h: {ThemePick.th.index.if(b1, 0n, ThemePick.th.index.if(b2, 1n, ThemePick.th.index.if(b3, 2n, None{}))) == Some{k} : Maybe<&2, Nat>})
  -> {TName.find.pick(b1, 0, TName.find.pick(b2, 1, TName.find.pick(b3, 2, TName.find(r, n)))) == TName.Res{U32.from_nat(k), False{}} : TName.Res}:
  match b1:
    case True{}:
      pk.res_at(0n, k, h)
    case False{}:
      match b2:
        case True{}:
          pk.res_at(1n, k, h)
        case False{}:
          match b3:
            case True{}:
              pk.res_at(2n, k, h)
            case False{}:
              LA.pt.none_some(Nat, k, {TName.find.pick(False{}, 0, TName.find.pick(False{}, 1, TName.find.pick(False{}, 2, TName.find(r, n)))) == TName.Res{U32.from_nat(k), False{}} : TName.Res}, h)

# a name of no builtin passes the builtins over
def pk.bn(b1: Bool, b2: Bool, b3: Bool, -r: List<&2, TName.Cand>, +n: String, h: {ThemePick.th.index.if(b1, 0n, ThemePick.th.index.if(b2, 1n, ThemePick.th.index.if(b3, 2n, None{}))) == None{} : Maybe<&2, Nat>})
  -> {TName.find.pick(b1, 0, TName.find.pick(b2, 1, TName.find.pick(b3, 2, TName.find(r, n)))) == TName.find(r, n) : TName.Res}:
  match b1:
    case True{}:
      pk.some_none(Nat, 0n, {TName.find.pick(True{}, 0, TName.find.pick(b2, 1, TName.find.pick(b3, 2, TName.find(r, n)))) == TName.find(r, n) : TName.Res}, h)
    case False{}:
      match b2:
        case True{}:
          pk.some_none(Nat, 1n, {TName.find.pick(False{}, 0, TName.find.pick(True{}, 1, TName.find.pick(b3, 2, TName.find(r, n)))) == TName.find(r, n) : TName.Res}, h)
        case False{}:
          match b3:
            case True{}:
              pk.some_none(Nat, 2n, {TName.find.pick(False{}, 0, TName.find.pick(False{}, 1, TName.find.pick(True{}, 2, TName.find(r, n)))) == TName.find(r, n) : TName.Res}, h)
            case False{}:
              {==}

# The cause
# ---------

def pk.blames(l: TChoice.Ld, +n: String) -> {TChoice.blames(l, n) == ThemePick.th.blames(l, n) : Bool}:
  match l:
    case TChoice.Fine{nm, c}:
      {==}
    case TChoice.Broke{nm, st}:
      match nm:
        case Some{x}:
          {==}
        case None{}:
          match st:
            case Some{s}:
              {==}
            case None{}:
              {==}

def pk.blame_none(ls: List<&2, TChoice.Ld>, +n: String, +at: Nat, +no: {ThemePick.th.none.blame(ls, n) == True{} : Bool}) -> {TChoice.cause.go(ls, n, at) == None{} : Maybe<&2, Nat>}:
  match ls:
    case Nil{}:
      {==}
    case Con{+l, +rest}:
      +hb = pk.not_t(ThemePick.th.blames(l, n), LA.themes.pt.and_l(Bool.not(ThemePick.th.blames(l, n)), ThemePick.th.none.blame(rest, n), no))
      %Equal.sym(Bool, TChoice.blames(l, n), False{}, Equal.trans(Bool, TChoice.blames(l, n), ThemePick.th.blames(l, n), False{}, pk.blames(l, n), hb)) : {TChoice.first.pick(_, at, TChoice.cause.go(rest, n, 1n+at)) == None{} : Maybe<&2, Nat>}
      pk.blame_none(rest, n, 1n+at, LA.themes.pt.and_r(Bool.not(ThemePick.th.blames(l, n)), ThemePick.th.none.blame(rest, n), no))

def pk.blame_first(pre: List<&2, TChoice.Ld>, +x: TChoice.Ld, +post: List<&2, TChoice.Ld>, +n: String, +at: Nat, +no: {ThemePick.th.none.blame(pre, n) == True{} : Bool}, bl: {ThemePick.th.blames(x, n) == True{} : Bool})
  -> {TChoice.cause.go(List.append(&2, TChoice.Ld, pre, x <> post), n, at) == Some{Nat.add(List.length(&2, TChoice.Ld, pre), at)} : Maybe<&2, Nat>}:
  match pre:
    case Nil{}:
      %Equal.sym(Bool, TChoice.blames(x, n), True{}, Equal.trans(Bool, TChoice.blames(x, n), ThemePick.th.blames(x, n), True{}, pk.blames(x, n), bl)) : {TChoice.first.pick(_, at, TChoice.cause.go(post, n, 1n+at)) == Some{at} : Maybe<&2, Nat>}
      {==}
    case Con{+l, +rest}:
      +hb = pk.not_t(ThemePick.th.blames(l, n), LA.themes.pt.and_l(Bool.not(ThemePick.th.blames(l, n)), ThemePick.th.none.blame(rest, n), no))
      %Equal.sym(Bool, TChoice.blames(l, n), False{}, Equal.trans(Bool, TChoice.blames(l, n), ThemePick.th.blames(l, n), False{}, pk.blames(l, n), hb)) : {TChoice.first.pick(_, at, TChoice.cause.go(List.append(&2, TChoice.Ld, rest, x <> post), n, 1n+at)) == Some{Nat.add(List.length(&2, TChoice.Ld, l <> rest), at)} : Maybe<&2, Nat>}
      %pk.add_succ(List.length(&2, TChoice.Ld, rest), at) : {TChoice.cause.go(List.append(&2, TChoice.Ld, rest, x <> post), n, 1n+at) == Some{_} : Maybe<&2, Nat>}
      pk.blame_first(rest, x, post, n, 1n+at, LA.themes.pt.and_r(Bool.not(ThemePick.th.blames(l, n)), ThemePick.th.none.blame(rest, n), no), bl)
