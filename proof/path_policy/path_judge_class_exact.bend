# eukhe: the proof of LAW path_judge_class_exact
#
# PROOF: the model's class is the spec's pick of three tests, each proved
# equal to the spec's: secret (LA.pp.any_under_spec), protected (the rule
# tests, the entries, the ancestor test over the entries and the secrets,
# and the names below the root: pc.below_root), and inside (a root holds
# the path: pc.has_root). pc.below_root rests on the root the model picks:
# a path that is a root is its own deepest root (pc.root_hit), a path that
# is none has its parent's (pc.root_of_up); a root at or above a path is
# never longer than it (pc.under_le), so `longer` keeps the deeper one.

import Base
import ../../bend/path_policy.bend as Pp
import ../../bend/tools.bend as Tl
import ../../laws/path_policy.bend as PathPolicy
import ../base/logic/logic.bend as LLogicLogic
import ./base.bend as LA
import ./secrets_need_yes.bend as PSecretsNeedYes

# Nat order
# ---------

def pc.lt_irrefl(n: Nat) -> {Nat.is_lt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      pc.lt_irrefl(k)

def pc.lt_succ(n: Nat) -> {Nat.is_lt(n, 1n+n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      pc.lt_succ(k)

# not (n < m) gives not (n + 1 < m)
def pc.nlt_succ_l(n: Nat, m: Nat, h: {Bool.not(Nat.is_lt(n, m)) == True{} : Bool}) -> {Bool.not(Nat.is_lt(1n+n, m)) == True{} : Bool}:
  match n:
    case 0n:
      match m:
        case 0n:
          {==}
        case 1n+k:
          LA.pp.absurdF({Bool.not(Nat.is_lt(1n, 1n+k)) == True{} : Bool}, h)
    case 1n+j:
      match m:
        case 0n:
          {==}
        case 1n+k:
          pc.nlt_succ_l(j, k, h)

# not (a < b) gives b < a + 1
def pc.nlt_lt(a: Nat, b: Nat, h: {Bool.not(Nat.is_lt(a, b)) == True{} : Bool}) -> {Nat.is_lt(b, 1n+a) == True{} : Bool}:
  match a:
    case 0n:
      match b:
        case 0n:
          {==}
        case 1n+k:
          LA.pp.absurdF({Nat.is_lt(1n+k, 1n) == True{} : Bool}, h)
    case 1n+i:
      match b:
        case 0n:
          {==}
        case 1n+j:
          pc.nlt_lt(i, j, h)

# an implication in Bool form, applied
def pc.mp(a: Bool, -b: Bool, ha: {a == True{} : Bool}, i: {Bool.or(Bool.not(a), b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      i
    case False{}:
      LA.pp.absurdF({b == True{} : Bool}, ha)

# Paths
# -----

def pc.nat_eq_refl(n: Nat) -> {Nat.is_eq(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+k:
      pc.nat_eq_refl(k)

def pc.ids_refl(xs: List<&2, Nat>) -> {Tl.ids.eq(xs, xs) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +xr:
      %Equal.sym(Bool, Nat.is_eq(x, x), True{}, pc.nat_eq_refl(x)) : {Bool.and(_, Tl.ids.eq(xr, xr)) == True{} : Bool}
      pc.ids_refl(xr)

def pc.under_refl(at: List<&2, Nat>) -> {Pp.under(at, at) == True{} : Bool}:
  match at:
    case Nil{}:
      {==}
    case +x <> +r:
      %Equal.sym(Bool, Tl.ids.eq(x <> r, x <> r), True{}, pc.ids_refl(x <> r)) : {Bool.or(_, Pp.under(x <> r, r)) == True{} : Bool}
      {==}

# a path at or above Nil is Nil: not (0 < its length)
def pc.ule_nil(b: Bool, +p: List<&2, Nat>, e: {Tl.ids.eq(p, Nil{}) == b : Bool}) -> {Bool.or(Bool.not(b), Bool.not(Nat.is_lt(0n, List.length(&2, Nat, p)))) == True{} : Bool}:
  match b:
    case True{}:
      Equal.cong(List<&2, Nat>, Bool, z => Bool.not(Nat.is_lt(0n, List.length(&2, Nat, z))), p, Nil{}, PSecretsNeedYes.pp.ids_sound(p, Nil{}, e))
    case False{}:
      {==}

# one step up: the path itself (b) or at or above its parent (c, ih)
def pc.ule_cons(b: Bool, c: Bool, +p: List<&2, Nat>, +y: Nat, +s: List<&2, Nat>, e: {Tl.ids.eq(p, y <> s) == b : Bool}, ih: {Bool.or(Bool.not(c), Bool.not(Nat.is_lt(List.length(&2, Nat, s), List.length(&2, Nat, p)))) == True{} : Bool}) -> {Bool.or(Bool.not(Bool.or(b, c)), Bool.not(Nat.is_lt(List.length(&2, Nat, y <> s), List.length(&2, Nat, p)))) == True{} : Bool}:
  match b:
    case True{}:
      Equal.trans(Bool, Bool.not(Nat.is_lt(List.length(&2, Nat, y <> s), List.length(&2, Nat, p))), Bool.not(Nat.is_lt(List.length(&2, Nat, y <> s), List.length(&2, Nat, y <> s))), True{}, Equal.cong(List<&2, Nat>, Bool, z => Bool.not(Nat.is_lt(List.length(&2, Nat, y <> s), List.length(&2, Nat, z))), p, y <> s, PSecretsNeedYes.pp.ids_sound(p, y <> s, e)), Equal.cong(Bool, Bool, z => Bool.not(z), Nat.is_lt(List.length(&2, Nat, y <> s), List.length(&2, Nat, y <> s)), False{}, pc.lt_irrefl(List.length(&2, Nat, y <> s))))
    case False{}:
      match c:
        case True{}:
          pc.nlt_succ_l(List.length(&2, Nat, s), List.length(&2, Nat, p), ih)
        case False{}:
          {==}

# a path at or above r is no longer than r
def pc.under_le(+p: List<&2, Nat>, r: List<&2, Nat>) -> {Bool.or(Bool.not(Pp.under(p, r)), Bool.not(Nat.is_lt(List.length(&2, Nat, r), List.length(&2, Nat, p)))) == True{} : Bool}:
  match r:
    case Nil{}:
      pc.ule_nil(Tl.ids.eq(p, Nil{}), p, {==})
    case +y <> +s:
      pc.ule_cons(Tl.ids.eq(p, y <> s), Pp.under(p, s), p, y, s, {==}, pc.under_le(p, s))

def pc.ule(+p: List<&2, Nat>, +r: List<&2, Nat>, h: {Pp.under(p, r) == True{} : Bool}) -> {Bool.not(Nat.is_lt(List.length(&2, Nat, r), List.length(&2, Nat, p))) == True{} : Bool}:
  pc.mp(Pp.under(p, r), Bool.not(Nat.is_lt(List.length(&2, Nat, r), List.length(&2, Nat, p))), h, pc.under_le(p, r))

# a path at or above at that is not at is shorter than at
def pc.strict(+p: List<&2, Nat>, at: List<&2, Nat>, es: {PathPolicy.pp_same(p, at) == False{} : Bool}, eh: {Pp.under(p, at) == True{} : Bool}) -> {Nat.is_lt(List.length(&2, Nat, p), List.length(&2, Nat, at)) == True{} : Bool}:
  match at:
    case Nil{}:
      LLogicLogic.pp.absurd({Nat.is_lt(List.length(&2, Nat, p), 0n) == True{} : Bool}, Equal.trans(Bool, True{}, Tl.ids.eq(p, Nil{}), False{}, Equal.sym(Bool, Tl.ids.eq(p, Nil{}), True{}, eh), Equal.trans(Bool, Tl.ids.eq(p, Nil{}), PathPolicy.pp_same(p, Nil{}), False{}, LA.pp.ids_same(p, Nil{}), es)))
    case +y <> +s:
      +ne = Equal.trans(Bool, Tl.ids.eq(p, y <> s), PathPolicy.pp_same(p, y <> s), False{}, LA.pp.ids_same(p, y <> s), es)
      +hs = Equal.trans(Bool, Pp.under(p, s), Bool.or(Tl.ids.eq(p, y <> s), Pp.under(p, s)), True{}, Equal.cong(Bool, Bool, z => Bool.or(z, Pp.under(p, s)), False{}, Tl.ids.eq(p, y <> s), Equal.sym(Bool, Tl.ids.eq(p, y <> s), False{}, ne)), eh)
      pc.nlt_lt(List.length(&2, Nat, s), List.length(&2, Nat, p), pc.ule(p, s, hs))

# The root the model picks
# ------------------------

# what root.of answers is at or above the path
def pc.RU(at: List<&2, Nat>, m: Maybe<&2, List<&2, Nat>>) -> Type:
  match m:
    case None{}:
      Unit
    case Some{b}:
      {Pp.under(b, at) == True{} : Bool}

def pc.ru_longer(c: Bool, -p: List<&2, Nat>, -b: List<&2, Nat>, -at: List<&2, Nat>, hp: {Pp.under(p, at) == True{} : Bool}, hb: {Pp.under(b, at) == True{} : Bool}) -> {Pp.under(Pp.longer.pick(c, p, b), at) == True{} : Bool}:
  match c:
    case True{}:
      hb
    case False{}:
      hp

def pc.ru_pick(hit: Bool, +p: List<&2, Nat>, +at: List<&2, Nat>, e: {Pp.under(p, at) == hit : Bool}, best: Maybe<&2, List<&2, Nat>>, hb: pc.RU(at, best)) -> pc.RU(at, Pp.root.pick(hit, p, best)):
  match hit:
    case False{}:
      hb
    case True{}:
      match best:
        case None{}:
          e
        case Some{+b}:
          pc.ru_longer(Nat.is_lt(List.length(&2, Nat, p), List.length(&2, Nat, b)), p, b, at, e, hb)

def pc.root_under(ro: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> pc.RU(at, Pp.root.of(ro, at)):
  match ro:
    case Nil{}:
      Unit{}
    case +p <> +rest:
      pc.ru_pick(Pp.under(p, at), p, at, {==}, Pp.root.of(rest, at), pc.root_under(rest, at))

# a root holds the path exactly when some root is at or above it
def pc.some_pick(hit: Bool, -p: List<&2, Nat>, best: Maybe<&2, List<&2, Nat>>) -> {Maybe.is_some(&2, List<&2, Nat>, Pp.root.pick(hit, p, best)) == Bool.or(hit, Maybe.is_some(&2, List<&2, Nat>, best)) : Bool}:
  match hit:
    case False{}:
      {==}
    case True{}:
      match best:
        case None{}:
          {==}
        case Some{b}:
          {==}

def pc.has_root(ro: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> {Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(ro, at)) == Pp.any_under(ro, at) : Bool}:
  match ro:
    case Nil{}:
      {==}
    case +p <> +rest:
      Equal.trans(Bool, Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(p <> rest, at)), Bool.or(Pp.under(p, at), Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(rest, at))), Bool.or(Pp.under(p, at), Pp.any_under(rest, at)), pc.some_pick(Pp.under(p, at), p, Pp.root.of(rest, at)), Equal.cong(Bool, Bool, z => Bool.or(Pp.under(p, at), z), Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(rest, at)), Pp.any_under(rest, at), pc.has_root(rest, at)))

# a path that is no root has the roots of its parent
def pc.root_of_up(ro: List<&2, List<&2, Nat>>, +x: Nat, +r: List<&2, Nat>, +h: {PathPolicy.pp_is_root(ro, x <> r) == False{} : Bool}) -> {Pp.root.of(ro, x <> r) == Pp.root.of(ro, r) : Maybe<&2, List<&2, Nat>>}:
  match ro:
    case Nil{}:
      {==}
    case +p <> +rest:
      +hp = PSecretsNeedYes.pp.or_false_l(PathPolicy.pp_same(p, x <> r), PathPolicy.pp_is_root(rest, x <> r), h)
      +hr = PSecretsNeedYes.pp.or_false_r(PathPolicy.pp_same(p, x <> r), PathPolicy.pp_is_root(rest, x <> r), h)
      %Equal.sym(Maybe<&2, List<&2, Nat>>, Pp.root.of(rest, x <> r), Pp.root.of(rest, r), pc.root_of_up(rest, x, r, hr)) : {Pp.root.pick(Bool.or(Tl.ids.eq(p, x <> r), Pp.under(p, r)), p, _) == Pp.root.pick(Pp.under(p, r), p, Pp.root.of(rest, r)) : Maybe<&2, List<&2, Nat>>}
      %Equal.sym(Bool, Tl.ids.eq(p, x <> r), False{}, Equal.trans(Bool, Tl.ids.eq(p, x <> r), PathPolicy.pp_same(p, x <> r), False{}, LA.pp.ids_same(p, x <> r), hp)) : {Pp.root.pick(Bool.or(_, Pp.under(p, r)), p, Pp.root.of(rest, r)) == Pp.root.pick(Pp.under(p, r), p, Pp.root.of(rest, r)) : Maybe<&2, List<&2, Nat>>}
      {==}

# a path that is a root is its own deepest root (when k holds)
def pc.REk(k: Bool, at: List<&2, Nat>, m: Maybe<&2, List<&2, Nat>>) -> Type:
  match k:
    case False{}:
      Unit
    case True{}:
      match m:
        case None{}:
          {True{} == False{} : Bool}
        case Some{b}:
          {Tl.ids.eq(at, b) == True{} : Bool}

def pc.RE(at: List<&2, Nat>, m: Maybe<&2, List<&2, Nat>>, k: Bool) -> Type:
  pc.REk(k, at, m)

# the longer of p (at itself) and b (at or above at) is p
def pc.hit_same(c: Bool, +p: List<&2, Nat>, +b: List<&2, Nat>, +at: List<&2, Nat>, ec: {Nat.is_lt(List.length(&2, Nat, p), List.length(&2, Nat, b)) == c : Bool}, same: {p == at : List<&2, Nat>}, nb: {Bool.not(Nat.is_lt(List.length(&2, Nat, at), List.length(&2, Nat, b))) == True{} : Bool}) -> {Tl.ids.eq(at, Pp.longer.pick(c, p, b)) == True{} : Bool}:
  match c:
    case True{}:
      +lt = Equal.trans(Bool, Nat.is_lt(List.length(&2, Nat, at), List.length(&2, Nat, b)), Nat.is_lt(List.length(&2, Nat, p), List.length(&2, Nat, b)), True{}, Equal.cong(List<&2, Nat>, Bool, z => Nat.is_lt(List.length(&2, Nat, z), List.length(&2, Nat, b)), at, p, Equal.sym(List<&2, Nat>, p, at, same)), ec)
      LA.pp.absurdF({Tl.ids.eq(at, b) == True{} : Bool}, Equal.trans(Bool, False{}, Bool.not(Nat.is_lt(List.length(&2, Nat, at), List.length(&2, Nat, b))), True{}, Equal.cong(Bool, Bool, z => Bool.not(z), True{}, Nat.is_lt(List.length(&2, Nat, at), List.length(&2, Nat, b)), Equal.sym(Bool, Nat.is_lt(List.length(&2, Nat, at), List.length(&2, Nat, b)), True{}, lt)), nb))
    case False{}:
      Equal.trans(Bool, Tl.ids.eq(at, p), Tl.ids.eq(at, at), True{}, Equal.cong(List<&2, Nat>, Bool, z => Tl.ids.eq(at, z), p, at, same), pc.ids_refl(at))

# the longer of p (strictly above at) and b (at itself) is b
def pc.hit_other(c: Bool, -p: List<&2, Nat>, +b: List<&2, Nat>, +at: List<&2, Nat>, ec: {Nat.is_lt(List.length(&2, Nat, p), List.length(&2, Nat, b)) == c : Bool}, lt: {Nat.is_lt(List.length(&2, Nat, p), List.length(&2, Nat, b)) == True{} : Bool}, hb: {Tl.ids.eq(at, b) == True{} : Bool}) -> {Tl.ids.eq(at, Pp.longer.pick(c, p, b)) == True{} : Bool}:
  match c:
    case True{}:
      hb
    case False{}:
      LA.pp.absurdF({Tl.ids.eq(at, p) == True{} : Bool}, Equal.trans(Bool, False{}, Nat.is_lt(List.length(&2, Nat, p), List.length(&2, Nat, b)), True{}, Equal.sym(Bool, Nat.is_lt(List.length(&2, Nat, p), List.length(&2, Nat, b)), False{}, ec), lt))

def pc.same_of(+p: List<&2, Nat>, +at: List<&2, Nat>, es: {PathPolicy.pp_same(p, at) == True{} : Bool}) -> {p == at : List<&2, Nat>}:
  PSecretsNeedYes.pp.ids_sound(p, at, Equal.trans(Bool, Tl.ids.eq(p, at), PathPolicy.pp_same(p, at), True{}, LA.pp.ids_same(p, at), es))

# p strictly above at, b at itself: the longer is b
def pc.other(+p: List<&2, Nat>, +b: List<&2, Nat>, +at: List<&2, Nat>, es: {PathPolicy.pp_same(p, at) == False{} : Bool}, eh: {Pp.under(p, at) == True{} : Bool}, +hb: {Tl.ids.eq(at, b) == True{} : Bool}) -> {Tl.ids.eq(at, Pp.longer.pick(Nat.is_lt(List.length(&2, Nat, p), List.length(&2, Nat, b)), p, b)) == True{} : Bool}:
  pc.hit_other(Nat.is_lt(List.length(&2, Nat, p), List.length(&2, Nat, b)), p, b, at, {==}, Equal.trans(Bool, Nat.is_lt(List.length(&2, Nat, p), List.length(&2, Nat, b)), Nat.is_lt(List.length(&2, Nat, p), List.length(&2, Nat, at)), True{}, Equal.cong(List<&2, Nat>, Bool, z => Nat.is_lt(List.length(&2, Nat, p), List.length(&2, Nat, z)), b, at, Equal.sym(List<&2, Nat>, at, b, PSecretsNeedYes.pp.ids_sound(at, b, hb))), pc.strict(p, at, es, eh)), hb)

def pc.hit_pick(s: Bool, k: Bool, hit: Bool, +p: List<&2, Nat>, +at: List<&2, Nat>, es: {PathPolicy.pp_same(p, at) == s : Bool}, eh: {Pp.under(p, at) == hit : Bool}, best: Maybe<&2, List<&2, Nat>>, ru: pc.RU(at, best), ih: pc.RE(at, best, k)) -> pc.RE(at, Pp.root.pick(hit, p, best), Bool.or(s, k)):
  match s:
    case True{}:
      match hit:
        case False{}:
          LLogicLogic.pp.absurd(pc.RE(at, Pp.root.pick(False{}, p, best), True{}), Equal.trans(Bool, True{}, Pp.under(p, at), False{}, Equal.trans(Bool, True{}, Pp.under(at, at), Pp.under(p, at), Equal.sym(Bool, Pp.under(at, at), True{}, pc.under_refl(at)), Equal.cong(List<&2, Nat>, Bool, z => Pp.under(z, at), at, p, Equal.sym(List<&2, Nat>, p, at, pc.same_of(p, at, es)))), eh))
        case True{}:
          match best:
            case None{}:
              Equal.trans(Bool, Tl.ids.eq(at, p), Tl.ids.eq(at, at), True{}, Equal.cong(List<&2, Nat>, Bool, z => Tl.ids.eq(at, z), p, at, pc.same_of(p, at, es)), pc.ids_refl(at))
            case Some{+b}:
              pc.hit_same(Nat.is_lt(List.length(&2, Nat, p), List.length(&2, Nat, b)), p, b, at, {==}, pc.same_of(p, at, es), pc.ule(b, at, ru))
    case False{}:
      match k:
        case False{}:
          Unit{}
        case True{}:
          match hit:
            case False{}:
              ih
            case True{}:
              match best:
                case None{}:
                  LLogicLogic.pp.absurd(pc.RE(at, Pp.root.pick(True{}, p, None{}), True{}), ih)
                case Some{+b}:
                  pc.other(p, b, at, es, eh, ih)

def pc.root_hit(ro: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> pc.RE(at, Pp.root.of(ro, at), PathPolicy.pp_is_root(ro, at)):
  match ro:
    case Nil{}:
      Unit{}
    case +p <> +rest:
      pc.hit_pick(PathPolicy.pp_same(p, at), PathPolicy.pp_is_root(rest, at), Pp.under(p, at), p, at, {==}, {==}, Pp.root.of(rest, at), pc.root_under(rest, at), pc.root_hit(rest, at))

# The names below the root
# ------------------------

def pc.below_nil(m: Maybe<&2, List<&2, Nat>>) -> {Pp.below(Nil{}, m) == Nil{} : List<&2, Nat>}:
  match m:
    case None{}:
      {==}
    case Some{b}:
      {==}

def pc.below_hit(+x: Nat, +r: List<&2, Nat>, m: Maybe<&2, List<&2, Nat>>, hit: pc.RE(x <> r, m, True{})) -> {Pp.below(x <> r, m) == Nil{} : List<&2, Nat>}:
  match m:
    case None{}:
      LLogicLogic.pp.absurd({Pp.below(x <> r, None{}) == Nil{} : List<&2, Nat>}, hit)
    case Some{b}:
      %Equal.sym(Bool, Tl.ids.eq(x <> r, b), True{}, hit) : {Pp.strip.pick(_, x, Pp.strip(r, b)) == Nil{} : List<&2, Nat>}
      {==}

def pc.miss_at(c: Bool, +x: Nat, +r: List<&2, Nat>, +b: List<&2, Nat>, -S: List<&2, Nat>, ec: {Tl.ids.eq(x <> r, b) == c : Bool}, ru: {Pp.under(b, r) == True{} : Bool}, ih: {Pp.strip(r, b) == S : List<&2, Nat>}) -> {Pp.strip.pick(c, x, Pp.strip(r, b)) == x <> S : List<&2, Nat>}:
  match c:
    case True{}:
      +u = pc.ule(b, r, ru)
      +cb = Equal.cong(List<&2, Nat>, Bool, z => Bool.not(Nat.is_lt(List.length(&2, Nat, r), List.length(&2, Nat, z))), x <> r, b, PSecretsNeedYes.pp.ids_sound(x <> r, b, ec))
      +cl = Equal.cong(Bool, Bool, z => Bool.not(z), Nat.is_lt(List.length(&2, Nat, r), 1n+List.length(&2, Nat, r)), True{}, pc.lt_succ(List.length(&2, Nat, r)))
      LA.pp.absurdF({Nil{} == x <> S : List<&2, Nat>}, Equal.trans(Bool, False{}, Bool.not(Nat.is_lt(List.length(&2, Nat, r), List.length(&2, Nat, x <> r))), True{}, Equal.sym(Bool, Bool.not(Nat.is_lt(List.length(&2, Nat, r), List.length(&2, Nat, x <> r))), False{}, cl), Equal.trans(Bool, Bool.not(Nat.is_lt(List.length(&2, Nat, r), List.length(&2, Nat, x <> r))), Bool.not(Nat.is_lt(List.length(&2, Nat, r), List.length(&2, Nat, b))), True{}, cb, u)))
    case False{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => x <> z, Pp.strip(r, b), S, ih)

def pc.below_miss(m: Maybe<&2, List<&2, Nat>>, +x: Nat, +r: List<&2, Nat>, -S: List<&2, Nat>, ru: pc.RU(r, m), ih: {Pp.below(r, m) == S : List<&2, Nat>}) -> {Pp.below(x <> r, m) == x <> S : List<&2, Nat>}:
  match m:
    case None{}:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => x <> z, r, S, ih)
    case Some{+b}:
      pc.miss_at(Tl.ids.eq(x <> r, b), x, r, b, S, {==}, ru, ih)

def pc.below_step(k: Bool, +ro: List<&2, List<&2, Nat>>, +x: Nat, +r: List<&2, Nat>, ek: {PathPolicy.pp_is_root(ro, x <> r) == k : Bool}, hit: pc.RE(x <> r, Pp.root.of(ro, x <> r), k), ru: pc.RU(r, Pp.root.of(ro, r)), ih: {Pp.below(r, Pp.root.of(ro, r)) == PathPolicy.pp_below_root(ro, r) : List<&2, Nat>}) -> {Pp.below(x <> r, Pp.root.of(ro, x <> r)) == PathPolicy.pp_below_pick(k, x, PathPolicy.pp_below_root(ro, r)) : List<&2, Nat>}:
  match k:
    case True{}:
      pc.below_hit(x, r, Pp.root.of(ro, x <> r), hit)
    case False{}:
      %Equal.sym(Maybe<&2, List<&2, Nat>>, Pp.root.of(ro, x <> r), Pp.root.of(ro, r), pc.root_of_up(ro, x, r, ek)) : {Pp.below(x <> r, _) == x <> PathPolicy.pp_below_root(ro, r) : List<&2, Nat>}
      pc.below_miss(Pp.root.of(ro, r), x, r, PathPolicy.pp_below_root(ro, r), ru, ih)

# the names the model's Named test reads are the spec's
def pc.below_root(+ro: List<&2, List<&2, Nat>>, at: List<&2, Nat>) -> {Pp.below(at, Pp.root.of(ro, at)) == PathPolicy.pp_below_root(ro, at) : List<&2, Nat>}:
  match at:
    case Nil{}:
      pc.below_nil(Pp.root.of(ro, Nil{}))
    case +x <> +r:
      pc.below_step(PathPolicy.pp_is_root(ro, x <> r), ro, x, r, {==}, pc.root_hit(ro, x <> r), pc.root_under(ro, r), pc.below_root(ro, r))

# The rules
# ---------

def pc.parent_eq(at: List<&2, Nat>, +p: List<&2, Nat>) -> {Pp.parent_is(at, p) == PathPolicy.pp_parent_is(at, p) : Bool}:
  match at:
    case Nil{}:
      {==}
    case x <> r:
      LA.pp.ids_same(r, p)

def pc.elem_eq(xs: List<&2, Nat>, +n: Nat) -> {Tl.elem(xs, n) == PathPolicy.pp_has_name(xs, n) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +y <> rest:
      %pc.elem_eq(rest, n) : {Bool.or(Nat.is_eq(y, n), Tl.elem(rest, n)) == Bool.or(Nat.is_eq(y, n), _) : Bool}
      {==}

def pc.covers_eq(r: Pp.Rule, +at: List<&2, Nat>, +low: List<&2, Nat>) -> {Pp.covers(r, at, low) == PathPolicy.pp_covers(r, at, low) : Bool}:
  match r:
    case Pp.Tree{+p}:
      LA.pp.under_spec(p, at)
    case Pp.Dir{+p}:
      %LA.pp.ids_same(at, p) : {Bool.or(Tl.ids.eq(at, p), Pp.parent_is(at, p)) == Bool.or(_, PathPolicy.pp_parent_is(at, p)) : Bool}
      %pc.parent_eq(at, p) : {Bool.or(Tl.ids.eq(at, p), Pp.parent_is(at, p)) == Bool.or(Tl.ids.eq(at, p), _) : Bool}
      {==}
    case Pp.Named{+n}:
      pc.elem_eq(low, n)

def pc.covers_any_eq(rs: List<&2, Pp.Rule>, +at: List<&2, Nat>, +low: List<&2, Nat>) -> {Pp.any_covers(rs, at, low) == PathPolicy.pp_covers_any(rs, at, low) : Bool}:
  match rs:
    case Nil{}:
      {==}
    case +r <> +rest:
      %pc.covers_eq(r, at, low) : {Bool.or(Pp.covers(r, at, low), Pp.any_covers(rest, at, low)) == Bool.or(_, PathPolicy.pp_covers_any(rest, at, low)) : Bool}
      %pc.covers_any_eq(rest, at, low) : {Bool.or(Pp.covers(r, at, low), Pp.any_covers(rest, at, low)) == Bool.or(Pp.covers(r, at, low), _) : Bool}
      {==}

def pc.entries_eq(rs: List<&2, Pp.Rule>) -> {Pp.entries(rs) == PathPolicy.pp_entries(rs) : List<&2, List<&2, Nat>>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case Pp.Tree{+p}:
          %pc.entries_eq(rest) : {p <> Pp.entries(rest) == p <> _ : List<&2, List<&2, Nat>>}
          {==}
        case Pp.Dir{+p}:
          %pc.entries_eq(rest) : {p <> Pp.entries(rest) == p <> _ : List<&2, List<&2, Nat>>}
          {==}
        case Pp.Named{n}:
          pc.entries_eq(rest)

def pc.or_assoc(a: Bool, +b: Bool, +c: Bool) -> {Bool.or(a, Bool.or(b, c)) == Bool.or(Bool.or(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def pc.anc_append(xs: List<&2, List<&2, Nat>>, +ys: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> {Pp.any_ancestor(List.append(&2, List<&2, Nat>, xs, ys), at) == Bool.or(Pp.any_ancestor(xs, at), Pp.any_ancestor(ys, at)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +p <> +rest:
      %Equal.sym(Bool, Pp.any_ancestor(List.append(&2, List<&2, Nat>, rest, ys), at), Bool.or(Pp.any_ancestor(rest, at), Pp.any_ancestor(ys, at)), pc.anc_append(rest, ys, at)) : {Bool.or(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), _) == Bool.or(Bool.or(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), Pp.any_ancestor(rest, at)), Pp.any_ancestor(ys, at)) : Bool}
      pc.or_assoc(Bool.and(Pp.under(at, p), Bool.not(Tl.ids.eq(at, p))), Pp.any_ancestor(rest, at), Pp.any_ancestor(ys, at))

# the model's protected test is the spec's
def pc.prot_eq(+ro: List<&2, List<&2, Nat>>, +ru: List<&2, Pp.Rule>, +se: List<&2, List<&2, Nat>>, +at: List<&2, Nat>) -> {Pp.protects(Pp.Pol{ro, ru, se}, at) == Bool.or(PathPolicy.pp_covers_any(ru, at, PathPolicy.pp_below_root(ro, at)), Bool.or(PathPolicy.pp_above_any(PathPolicy.pp_entries(ru), at), PathPolicy.pp_above_any(se, at))) : Bool}:
  %pc.below_root(ro, at) : {Pp.protects(Pp.Pol{ro, ru, se}, at) == Bool.or(PathPolicy.pp_covers_any(ru, at, _), Bool.or(PathPolicy.pp_above_any(PathPolicy.pp_entries(ru), at), PathPolicy.pp_above_any(se, at))) : Bool}
  %pc.covers_any_eq(ru, at, Pp.below(at, Pp.root.of(ro, at))) : {Pp.protects(Pp.Pol{ro, ru, se}, at) == Bool.or(_, Bool.or(PathPolicy.pp_above_any(PathPolicy.pp_entries(ru), at), PathPolicy.pp_above_any(se, at))) : Bool}
  %pc.entries_eq(ru) : {Pp.protects(Pp.Pol{ro, ru, se}, at) == Bool.or(Pp.any_covers(ru, at, Pp.below(at, Pp.root.of(ro, at))), Bool.or(PathPolicy.pp_above_any(_, at), PathPolicy.pp_above_any(se, at))) : Bool}
  %LA.pp.any_ancestor_spec(Pp.entries(ru), at) : {Pp.protects(Pp.Pol{ro, ru, se}, at) == Bool.or(Pp.any_covers(ru, at, Pp.below(at, Pp.root.of(ro, at))), Bool.or(_, PathPolicy.pp_above_any(se, at))) : Bool}
  %LA.pp.any_ancestor_spec(se, at) : {Pp.protects(Pp.Pol{ro, ru, se}, at) == Bool.or(Pp.any_covers(ru, at, Pp.below(at, Pp.root.of(ro, at))), Bool.or(Pp.any_ancestor(Pp.entries(ru), at), _)) : Bool}
  %pc.anc_append(Pp.entries(ru), se, at) : {Pp.protects(Pp.Pol{ro, ru, se}, at) == Bool.or(Pp.any_covers(ru, at, Pp.below(at, Pp.root.of(ro, at))), _) : Bool}
  {==}

# The class
# ---------

def pc.pick_eq(s: Bool, p: Bool, i: Bool, l: Bool) -> {Pp.demote(Pp.cls.pick(s, p, i), l) == PathPolicy.pp_cls_pick(s, p, Bool.and(i, Bool.not(l))) : Pp.Cls}:
  match s:
    case True{}:
      {==}
    case False{}:
      match p:
        case True{}:
          {==}
        case False{}:
          match i:
            case True{}:
              match l:
                case True{}:
                  {==}
                case False{}:
                  {==}
            case False{}:
              {==}

def PathPolicy.path_judge_class_exact(ro, ru, se, at, l):
  %LA.pp.any_under_spec(se, at) : {Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l})) == PathPolicy.pp_cls_pick(_, Bool.or(PathPolicy.pp_covers_any(ru, at, PathPolicy.pp_below_root(ro, at)), Bool.or(PathPolicy.pp_above_any(PathPolicy.pp_entries(ru), at), PathPolicy.pp_above_any(se, at))), Bool.and(PathPolicy.pp_under_any(ro, at), Bool.not(l))) : Pp.Cls}
  %pc.prot_eq(ro, ru, se, at) : {Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l})) == PathPolicy.pp_cls_pick(Pp.any_under(se, at), _, Bool.and(PathPolicy.pp_under_any(ro, at), Bool.not(l))) : Pp.Cls}
  %LA.pp.any_under_spec(ro, at) : {Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l})) == PathPolicy.pp_cls_pick(Pp.any_under(se, at), Pp.protects(Pp.Pol{ro, ru, se}, at), Bool.and(_, Bool.not(l))) : Pp.Cls}
  %pc.has_root(ro, at) : {Pp.Judged.cls(Pp.judge(Pp.Pol{ro, ru, se}, Pp.Res{at, l})) == PathPolicy.pp_cls_pick(Pp.any_under(se, at), Pp.protects(Pp.Pol{ro, ru, se}, at), Bool.and(_, Bool.not(l))) : Pp.Cls}
  pc.pick_eq(Pp.any_under(se, at), Pp.protects(Pp.Pol{ro, ru, se}, at), Maybe.is_some(&2, List<&2, Nat>, Pp.root.of(ro, at)), l)
