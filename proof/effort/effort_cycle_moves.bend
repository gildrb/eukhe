# eukhe: the proof of LAW effort_cycle_moves
#
# With two or more offered levels the step starts at the clamp, an offered
# level (LA.pe.clamp_in), and a scan of a list that has its start finds it
# (cm.fwd_some, cm.bwd_some); with fewer it gives none. Two or more is a
# count of two or more (cm.two_len). The level a step gives is offered
# (cm.cycle_in): the scan gives a level of the list or one of its ends.

import Base
import ../../bend/effort.bend as Ef
import ../../laws/effort/depth.bend as Effort
import ./base.bend as LA

def cm.MI(m: Maybe<&2, Ef.Lv>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def cm.none_some(-b: Ef.Lv, -G: Type, e: {None{} == Some{b} : Maybe<&2, Ef.Lv>}) -> G:
  %e : cm.MI(_, G)
  Unit{}

def cm.some_inj(-a: Ef.Lv, -b: Ef.Lv, e: {Some{a} == Some{b} : Maybe<&2, Ef.Lv>}) -> {a == b : Ef.Lv}:
  Equal.cong(Maybe<&2, Ef.Lv>, Ef.Lv, m => Maybe.default(&2, Ef.Lv, m, a), Some{a}, Some{b}, e)

def cm.le0(n: Nat) -> {True{} == Nat.is_le(0n, n) : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+q:
      {==}

# at least two levels: a count of two or more
def cm.two_len(xs: List<&2, Ef.Lv>) -> {Ef.two(xs) == Nat.is_le(2n, List.length(&2, Ef.Lv, xs)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      match rest:
        case Nil{}:
          {==}
        case y <> more:
          cm.le0(List.length(&2, Ef.Lv, more))

# every level of xs is in lad
def cm.allin(xs: List<&2, Ef.Lv>, +lad: List<&2, Ef.Lv>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> rest:
      Bool.and(Ef.has(lad, x), cm.allin(rest, lad))

def cm.allin_cons(xs: List<&2, Ef.Lv>, +y: Ef.Lv, +lad: List<&2, Ef.Lv>, +h: {cm.allin(xs, lad) == True{} : Bool}) -> {cm.allin(xs, y <> lad) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +rest:
      +hx = LA.pe.and_l(Ef.has(lad, x), cm.allin(rest, lad), h)
      +hr = LA.pe.and_r(Ef.has(lad, x), cm.allin(rest, lad), h)
      LA.pe.and_t(Ef.has(y <> lad, x), cm.allin(rest, y <> lad), LA.pe.or_r(Ef.Lv.eq(y, x), Ef.has(lad, x), hx), cm.allin_cons(rest, y, lad, hr))

def cm.allin_self(lad: List<&2, Ef.Lv>) -> {cm.allin(lad, lad) == True{} : Bool}:
  match lad:
    case Nil{}:
      {==}
    case +x <> +rest:
      %LA.pe.lv_refl(x) : {Bool.and(Bool.or(_, Ef.has(rest, x)), cm.allin(rest, x <> rest)) == True{} : Bool}
      cm.allin_cons(rest, x, rest, cm.allin_self(rest))

# the first level of xs, else d, is in lad
def cm.first_in(xs: List<&2, Ef.Lv>, +lad: List<&2, Ef.Lv>, d: Ef.Lv, all: {cm.allin(xs, lad) == True{} : Bool}, hd: {Ef.has(lad, d) == True{} : Bool}) -> {Ef.has(lad, Ef.first(xs, d)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hd
    case x <> rest:
      LA.pe.and_l(Ef.has(lad, x), cm.allin(rest, lad), all)

# the last level of xs, else d, is in lad
def cm.last_in(xs: List<&2, Ef.Lv>, +lad: List<&2, Ef.Lv>, d: Ef.Lv, +all: {cm.allin(xs, lad) == True{} : Bool}, hd: {Ef.has(lad, d) == True{} : Bool}) -> {Ef.has(lad, Ef.last(xs, d)) == True{} : Bool}:
  match xs:
    case Nil{}:
      hd
    case +x <> +rest:
      cm.last_in(rest, lad, x, LA.pe.and_r(Ef.has(lad, x), cm.allin(rest, lad), all), LA.pe.and_l(Ef.has(lad, x), cm.allin(rest, lad), all))

# a forward scan of levels in lad gives a level in lad
def cm.fwd_in(xs: List<&2, Ef.Lv>, +lad: List<&2, Ef.Lv>, +c: Ef.Lv, +top: Ef.Lv, hit: Bool, +all: {cm.allin(xs, lad) == True{} : Bool}, +ht: {Ef.has(lad, top) == True{} : Bool}, -k: Ef.Lv, e: {Ef.fwd.go(xs, c, top, hit) == Some{k} : Maybe<&2, Ef.Lv>}) -> {Ef.has(lad, k) == True{} : Bool}:
  match xs:
    case Nil{}:
      cm.none_some(k, {Ef.has(lad, k) == True{} : Bool}, e)
    case x <> +rest:
      match hit:
        case True{}:
          %cm.some_inj(Ef.first(rest, top), k, e) : {Ef.has(lad, _) == True{} : Bool}
          cm.first_in(rest, lad, top, LA.pe.and_r(Ef.has(lad, x), cm.allin(rest, lad), all), ht)
        case False{}:
          cm.fwd_in(rest, lad, c, top, Ef.at(rest, c), LA.pe.and_r(Ef.has(lad, x), cm.allin(rest, lad), all), ht, k, e)

# a backward scan of levels in lad gives a level in lad
def cm.bwd_in(xs: List<&2, Ef.Lv>, +lad: List<&2, Ef.Lv>, +c: Ef.Lv, prev: Ef.Lv, hit: Bool, +all: {cm.allin(xs, lad) == True{} : Bool}, hp: {Ef.has(lad, prev) == True{} : Bool}, -k: Ef.Lv, e: {Ef.bwd.go(xs, c, prev, hit) == Some{k} : Maybe<&2, Ef.Lv>}) -> {Ef.has(lad, k) == True{} : Bool}:
  match xs:
    case Nil{}:
      cm.none_some(k, {Ef.has(lad, k) == True{} : Bool}, e)
    case +x <> +rest:
      match hit:
        case True{}:
          %cm.some_inj(prev, k, e) : {Ef.has(lad, _) == True{} : Bool}
          hp
        case False{}:
          cm.bwd_in(rest, lad, c, x, Ef.at(rest, c), LA.pe.and_r(Ef.has(lad, x), cm.allin(rest, lad), all), LA.pe.and_l(Ef.has(lad, x), cm.allin(rest, lad), all), k, e)

# a forward scan of a list that has c gives a level
def cm.fwd_some(xs: List<&2, Ef.Lv>, +c: Ef.Lv, top: Ef.Lv, hit: Bool, eh: {Ef.at(xs, c) == hit : Bool}, in: {Ef.has(xs, c) == True{} : Bool}) -> {Maybe.is_some(&2, Ef.Lv, Ef.fwd.go(xs, c, top, hit)) == True{} : Bool}:
  match xs:
    case Nil{}:
      LA.pe.absurdF({Maybe.is_some(&2, Ef.Lv, Ef.fwd.go(Nil{}, c, top, hit)) == True{} : Bool}, in)
    case x <> +rest:
      match hit:
        case True{}:
          {==}
        case False{}:
          cm.fwd_some(rest, c, top, Ef.at(rest, c), {==}, LA.pe.or_l_false(Ef.Lv.eq(x, c), Ef.has(rest, c), eh, in))

def cm.bwd_some(xs: List<&2, Ef.Lv>, +c: Ef.Lv, prev: Ef.Lv, hit: Bool, eh: {Ef.at(xs, c) == hit : Bool}, in: {Ef.has(xs, c) == True{} : Bool}) -> {Maybe.is_some(&2, Ef.Lv, Ef.bwd.go(xs, c, prev, hit)) == True{} : Bool}:
  match xs:
    case Nil{}:
      LA.pe.absurdF({Maybe.is_some(&2, Ef.Lv, Ef.bwd.go(Nil{}, c, prev, hit)) == True{} : Bool}, in)
    case +x <> +rest:
      match hit:
        case True{}:
          {==}
        case False{}:
          cm.bwd_some(rest, c, x, Ef.at(rest, c), {==}, LA.pe.or_l_false(Ef.Lv.eq(x, c), Ef.has(rest, c), eh, in))

# a list of two or more levels is not empty
def cm.ne(lad: List<&2, Ef.Lv>, tw: {Ef.two(lad) == True{} : Bool}) -> {Ef.empty(lad) == False{} : Bool}:
  match lad:
    case Nil{}:
      LA.pe.absurdF({Ef.empty(Nil{}) == False{} : Bool}, tw)
    case x <> rest:
      {==}

# a step from a level of lad gives a level
def cm.move_some(d: Ef.Dir, +lad: List<&2, Ef.Lv>, +c: Ef.Lv, in: {Ef.has(lad, c) == True{} : Bool}) -> {Maybe.is_some(&2, Ef.Lv, Ef.move(d, lad, c)) == True{} : Bool}:
  match d:
    case Ef.Forward{}:
      cm.fwd_some(lad, c, Ef.first(lad, Ef.Off{}), Ef.at(lad, c), {==}, in)
    case Ef.Backward{}:
      cm.bwd_some(lad, c, Ef.last(lad, Ef.Off{}), Ef.at(lad, c), {==}, in)

def cm.at_some(b: Bool, +lad: List<&2, Ef.Lv>, +l: Ef.Lv, d: Ef.Dir, eb: {Ef.two(lad) == b : Bool}) -> {Maybe.is_some(&2, Ef.Lv, Ef.cycle.at(b, lad, l, d)) == b : Bool}:
  match b:
    case True{}:
      cm.move_some(d, lad, Ef.clamp.in(lad, l), LA.pe.clamp_in(lad, l, cm.ne(lad, eb)))
    case False{}:
      {==}

# the ends of a list of two or more levels are among them
def cm.first_end(lad: List<&2, Ef.Lv>, tw: {Ef.two(lad) == True{} : Bool}) -> {Ef.has(lad, Ef.first(lad, Ef.Off{})) == True{} : Bool}:
  match lad:
    case Nil{}:
      LA.pe.absurdF({Ef.has(Nil{}, Ef.Off{}) == True{} : Bool}, tw)
    case +x <> +rest:
      LA.pe.and_l(Ef.has(x <> rest, x), cm.allin(rest, x <> rest), cm.allin_self(x <> rest))

def cm.last_end(lad: List<&2, Ef.Lv>, tw: {Ef.two(lad) == True{} : Bool}) -> {Ef.has(lad, Ef.last(lad, Ef.Off{})) == True{} : Bool}:
  match lad:
    case Nil{}:
      LA.pe.absurdF({Ef.has(Nil{}, Ef.Off{}) == True{} : Bool}, tw)
    case +x <> +rest:
      +all = cm.allin_self(x <> rest)
      cm.last_in(rest, x <> rest, x, LA.pe.and_r(Ef.has(x <> rest, x), cm.allin(rest, x <> rest), all), LA.pe.and_l(Ef.has(x <> rest, x), cm.allin(rest, x <> rest), all))

# a step along a list of two or more levels gives one of them
def cm.move_in(d: Ef.Dir, +lad: List<&2, Ef.Lv>, +c: Ef.Lv, +tw: {Ef.two(lad) == True{} : Bool}, -k: Ef.Lv, e: {Ef.move(d, lad, c) == Some{k} : Maybe<&2, Ef.Lv>}) -> {Ef.has(lad, k) == True{} : Bool}:
  match d:
    case Ef.Forward{}:
      cm.fwd_in(lad, lad, c, Ef.first(lad, Ef.Off{}), Ef.at(lad, c), cm.allin_self(lad), cm.first_end(lad, tw), k, e)
    case Ef.Backward{}:
      cm.bwd_in(lad, lad, c, Ef.last(lad, Ef.Off{}), Ef.at(lad, c), cm.allin_self(lad), cm.last_end(lad, tw), k, e)

def cm.at_in(b: Bool, +lad: List<&2, Ef.Lv>, +l: Ef.Lv, d: Ef.Dir, eb: {Ef.two(lad) == b : Bool}, -k: Ef.Lv, e: {Ef.cycle.at(b, lad, l, d) == Some{k} : Maybe<&2, Ef.Lv>}) -> {Ef.has(lad, k) == True{} : Bool}:
  match b:
    case True{}:
      cm.move_in(d, lad, Ef.clamp.in(lad, l), eb, k, e)
    case False{}:
      cm.none_some(k, {Ef.has(lad, k) == True{} : Bool}, e)

# the level a cycle step gives is offered
def cm.cycle_in(+m: Ef.Mdl, +l: Ef.Lv, d: Ef.Dir, -k: Ef.Lv, e: {Ef.cycle(m, l, d) == Some{k} : Maybe<&2, Ef.Lv>}) -> {Ef.has(Ef.offered(m), k) == True{} : Bool}:
  cm.at_in(Ef.two(Ef.offered(m)), Ef.offered(m), l, d, {==}, k, e)

def Effort.effort_cycle_moves(m, l, d):
  +lad = Ef.offered(m)
  Equal.trans(Bool, Maybe.is_some(&2, Ef.Lv, Ef.cycle(m, l, d)), Ef.two(lad), Nat.is_le(2n, List.length(&2, Ef.Lv, lad)), cm.at_some(Ef.two(lad), lad, l, d, {==}), cm.two_len(lad))
