# eukhe: the search of `first` visits the places of the text in order
# (laws/shape/search.bend R7): the spec's walk sp_find.go, started at the
# text start, is at the place after u of the text u ++ v when it reads v
# (slm.G); it answers the first of those places with an answer (slm.lm:
# none before; slm.fp: that one), and none when no place it may start at
# has one (slm.nl).

import Base
import ../../../bend/shape.bend as S
import ../../../laws/shape/match.bend as Shape
import ../../../laws/shape/search.bend as ShapeSearch

# Logic
# -----

def slm.MIf(m: Maybe<&2, S.Hit>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def slm.none_some(-G: Type, -y: S.Hit, e: {None{} == Some{y} : Maybe<&2, S.Hit>}) -> G:
  %e : slm.MIf(_, G)
  Unit{}

def slm.some_none(-G: Type, -y: S.Hit, e: {Some{y} == None{} : Maybe<&2, S.Hit>}) -> G:
  slm.none_some(G, y, Equal.sym(Maybe<&2, S.Hit>, Some{y}, None{}, e))

def slm.BIf(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def slm.false_true(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : slm.BIf(_, G)
  Unit{}

def slm.hit_r(m: Maybe<&2, S.Hit>, d: S.St) -> S.St:
  match m:
    case None{}:
      d
    case Some{h}:
      match h:
        case S.Hit{r, p}:
          r

def slm.hit_p(m: Maybe<&2, S.Hit>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{h}:
      match h:
        case S.Hit{r, p}:
          p

# Nat
# ---

def slm.lt_irrefl(n: Nat) -> {Nat.is_lt(n, n) == False{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      slm.lt_irrefl(p)

def slm.le_zero(n: Nat) -> {Nat.is_le(0n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      {==}

# a at most b: b is not below a
def slm.le_nlt(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.is_lt(b, a) == False{} : Bool}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      {==}
    case 1n+p 0n:
      slm.false_true({Nat.is_lt(0n, 1n+p) == False{} : Bool}, h)
    case 1n+p 1n+q:
      slm.le_nlt(p, q, h)

# Texts
# -----

def slm.app_nil(u: String) -> {String.append(u, SNil{}) == u : String}:
  match u:
    case SNil{}:
      {==}
    case SCon{+x, t}:
      Equal.cong(String, String, z => SCon{x, z}, String.append(t, SNil{}), t, slm.app_nil(t))

# u, then x, then a: u then x <> a
def slm.app_snoc(u: String, +x: Char, +a: String) -> {String.append(String.append(u, SCon{x, SNil{}}), a) == String.append(u, SCon{x, a}) : String}:
  match u:
    case SNil{}:
      {==}
    case SCon{+y, t}:
      Equal.cong(String, String, z => SCon{y, z}, String.append(String.append(t, SCon{x, SNil{}}), a), String.append(t, SCon{x, a}), slm.app_snoc(t, x, a))

def slm.len_snoc(u: String, +x: Char) -> {String.length(String.append(u, SCon{x, SNil{}})) == 1n+String.length(u) : Nat}:
  match u:
    case SNil{}:
      {==}
    case SCon{y, t}:
      Equal.cong(Nat, Nat, z => 1n+z, String.length(String.append(t, SCon{x, SNil{}})), 1n+String.length(t), slm.len_snoc(t, x))

def slm.len_le(u: String, +z: String) -> {Nat.is_le(String.length(u), String.length(String.append(u, z))) == True{} : Bool}:
  match u:
    case SNil{}:
      slm.le_zero(String.length(z))
    case SCon{y, t}:
      slm.len_le(t, z)

def slm.ew_go(u: String, +x: Char, w: Bool) -> {ShapeSearch.sp_ends_word.go(String.append(u, SCon{x, SNil{}}), w) == Shape.sp_word(x) : Bool}:
  match u:
    case SNil{}:
      {==}
    case SCon{+y, t}:
      slm.ew_go(t, x, Shape.sp_word(y))

# The walk
# --------

# the walk at the place after u of the text u ++ v, reading v
def slm.G(+st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +u: String, +v: String) -> Maybe<&2, S.Hit>:
  ShapeSearch.sp_find.go(v, f, st, ps, ends, String.length(u), String.length(v), ShapeSearch.sp_ends_word(u), ShapeSearch.sp_none_caps(n))

# the answer at the place after u of the text u ++ v
def slm.A(+ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +u: String, +v: String) -> Maybe<&2, S.St>:
  Shape.sp_answer(f, ps, ends, ShapeSearch.sp_place(u, v, n))

# one char on: the walk's next state is the place after u ++ [x]
def slm.step(+st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +u: String, +x: Char, +t: String) -> {ShapeSearch.sp_find.go(t, f, st, ps, ends, 1n+String.length(u), String.length(t), Shape.sp_word(x), ShapeSearch.sp_none_caps(n)) == slm.G(st, ps, ends, f, n, String.append(u, SCon{x, SNil{}}), t) : Maybe<&2, S.Hit>}:
  +ux = String.append(u, SCon{x, SNil{}})
  %Equal.sym(Nat, String.length(ux), 1n+String.length(u), slm.len_snoc(u, x)) : {ShapeSearch.sp_find.go(t, f, st, ps, ends, 1n+String.length(u), String.length(t), Shape.sp_word(x), ShapeSearch.sp_none_caps(n)) == ShapeSearch.sp_find.go(t, f, st, ps, ends, _, String.length(t), ShapeSearch.sp_ends_word(ux), ShapeSearch.sp_none_caps(n)) : Maybe<&2, S.Hit>}
  %Equal.sym(Bool, ShapeSearch.sp_ends_word(ux), Shape.sp_word(x), slm.ew_go(u, x, False{})) : {ShapeSearch.sp_find.go(t, f, st, ps, ends, 1n+String.length(u), String.length(t), Shape.sp_word(x), ShapeSearch.sp_none_caps(n)) == ShapeSearch.sp_find.go(t, f, st, ps, ends, 1n+String.length(u), String.length(t), _, ShapeSearch.sp_none_caps(n)) : Maybe<&2, S.Hit>}
  {==}

# the answer at the place after u ++ [x], then a, is the one after u, then x <> a
def slm.A_snoc(+ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +u: String, +x: Char, +a: String, +b: String) -> {slm.A(ps, ends, f, n, String.append(String.append(u, SCon{x, SNil{}}), a), b) == slm.A(ps, ends, f, n, String.append(u, SCon{x, a}), b) : Maybe<&2, S.St>}:
  Equal.cong(String, Maybe<&2, S.St>, z => slm.A(ps, ends, f, n, z, b), String.append(String.append(u, SCon{x, SNil{}}), a), String.append(u, SCon{x, a}), slm.app_snoc(u, x, a))

# The first test
# --------------

def slm.le_refl(n: Nat) -> {Nat.is_le(n, n) == True{} : Bool}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      slm.le_refl(p)

# a place L with an answer at char p = L, and a place X at or past L
# below p: impossible
def slm.no_early(-G: Type, +X: Nat, +L: Nat, +p: Nat, ep: {L == p : Nat}, hle: {Nat.is_le(L, X) == True{} : Bool}, early: {Nat.is_lt(X, p) == True{} : Bool}) -> G:
  +e1 = Equal.trans(Bool, Nat.is_lt(X, L), Nat.is_lt(X, p), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(X, z), L, p, ep), early)
  slm.false_true(G, Equal.trans(Bool, False{}, Nat.is_lt(X, L), True{}, Equal.sym(Bool, Nat.is_lt(X, L), False{}, slm.le_nlt(L, X, hle)), e1))

# the walk's first test, its answer rewritten
def slm.via(-m0: Maybe<&2, S.St>, -m: Maybe<&2, S.St>, em: {m0 == m : Maybe<&2, S.St>}, -L: Nat, -R: Unit -> Maybe<&2, S.Hit>, -g: Maybe<&2, S.Hit>, hG: {ShapeSearch.sp_try(m0, L, R) == g : Maybe<&2, S.Hit>}) -> {ShapeSearch.sp_try(m, L, R) == g : Maybe<&2, S.Hit>}:
  Equal.trans(Maybe<&2, S.Hit>, ShapeSearch.sp_try(m, L, R), ShapeSearch.sp_try(m0, L, R), g, Equal.cong(Maybe<&2, S.St>, Maybe<&2, S.Hit>, z => ShapeSearch.sp_try(z, L, R), m, m0, Equal.sym(Maybe<&2, S.St>, m0, m, em)), hG)

# a found place: its char count and its answer
def slm.found_p(+r0: S.St, +L: Nat, +r: S.St, +p: Nat, h: {Some{S.Hit{r0, L}} == Some{S.Hit{r, p}} : Maybe<&2, S.Hit>}) -> {L == p : Nat}:
  Equal.cong(Maybe<&2, S.Hit>, Nat, z => slm.hit_p(z), Some{S.Hit{r0, L}}, Some{S.Hit{r, p}}, h)

def slm.found_r(+r0: S.St, +L: Nat, +r: S.St, +p: Nat, h: {Some{S.Hit{r0, L}} == Some{S.Hit{r, p}} : Maybe<&2, S.Hit>}) -> {r0 == r : S.St}:
  Equal.cong(Maybe<&2, S.Hit>, S.St, z => slm.hit_r(z, r0), Some{S.Hit{r0, L}}, Some{S.Hit{r, p}}, h)

# the first place tested, answer m: none when the walk answers at a later
# char
def slm.lm0(+ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +w: String, +v: String, m: Maybe<&2, S.St>, em: {slm.A(ps, ends, f, n, w, v) == m : Maybe<&2, S.St>}, -R: Unit -> Maybe<&2, S.Hit>, +r: S.St, +p: Nat, hG: {ShapeSearch.sp_try(slm.A(ps, ends, f, n, w, v), String.length(w), R) == Some{S.Hit{r, p}} : Maybe<&2, S.Hit>}, early: {Nat.is_lt(String.length(w), p) == True{} : Bool}) -> {slm.A(ps, ends, f, n, w, v) == None{} : Maybe<&2, S.St>}:
  match m:
    case None{}:
      em
    case Some{+r0}:
      +h2 = slm.via(slm.A(ps, ends, f, n, w, v), Some{r0}, em, String.length(w), R, Some{S.Hit{r, p}}, hG)
      slm.no_early({slm.A(ps, ends, f, n, w, v) == None{} : Maybe<&2, S.St>}, String.length(w), String.length(w), p, slm.found_p(r0, String.length(w), r, p, h2), slm.le_refl(String.length(w)), early)

# the walk's test of a place after w with chars left, then the next place
def slm.R(+st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +w: String, +x: Char, +t: String) -> Unit -> Maybe<&2, S.Hit>:
  k => ShapeSearch.sp_next(st, j => ShapeSearch.sp_find.go(t, f, st, ps, ends, 1n+String.length(w), String.length(t), Shape.sp_word(x), ShapeSearch.sp_none_caps(n)))

# the next place of an Anywhere walk is the place after w ++ [x]
def slm.next(+ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +w: String, +x: Char, +t: String, -g: Maybe<&2, S.Hit>, h2: {slm.R(S.Anywhere{}, ps, ends, f, n, w, x, t)(Unit{}) == g : Maybe<&2, S.Hit>}) -> {slm.G(S.Anywhere{}, ps, ends, f, n, String.append(w, SCon{x, SNil{}}), t) == g : Maybe<&2, S.Hit>}:
  +NX = ShapeSearch.sp_find.go(t, f, S.Anywhere{}, ps, ends, 1n+String.length(w), String.length(t), Shape.sp_word(x), ShapeSearch.sp_none_caps(n))
  Equal.trans(Maybe<&2, S.Hit>, slm.G(S.Anywhere{}, ps, ends, f, n, String.append(w, SCon{x, SNil{}}), t), NX, g, Equal.sym(Maybe<&2, S.Hit>, NX, slm.G(S.Anywhere{}, ps, ends, f, n, String.append(w, SCon{x, SNil{}}), t), slm.step(S.Anywhere{}, ps, ends, f, n, w, x, t)), h2)

# Leftmost
# --------

# the walk from the place after w answers at char p: no place after w ++ u
# below p has an answer (m: the answer after w)
def slm.lm(u: String, +st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +w: String, +v: String, +r: S.St, +p: Nat, m: Maybe<&2, S.St>, em: {slm.A(ps, ends, f, n, w, String.append(u, v)) == m : Maybe<&2, S.St>}, hG: {slm.G(st, ps, ends, f, n, w, String.append(u, v)) == Some{S.Hit{r, p}} : Maybe<&2, S.Hit>}, early: {Nat.is_lt(String.length(String.append(w, u)), p) == True{} : Bool}) -> {slm.A(ps, ends, f, n, String.append(w, u), v) == None{} : Maybe<&2, S.St>}:
  match u:
    case SNil{}:
      match v:
        case SNil{}:
          +early0 = Equal.trans(Bool, Nat.is_lt(String.length(w), p), Nat.is_lt(String.length(String.append(w, SNil{})), p), True{}, Equal.cong(String, Bool, z => Nat.is_lt(String.length(z), p), w, String.append(w, SNil{}), Equal.sym(String, String.append(w, SNil{}), w, slm.app_nil(w))), early)
          %Equal.sym(String, String.append(w, SNil{}), w, slm.app_nil(w)) : {slm.A(ps, ends, f, n, _, SNil{}) == None{} : Maybe<&2, S.St>}
          slm.lm0(ps, ends, f, n, w, SNil{}, slm.A(ps, ends, f, n, w, SNil{}), {==}, k => None{}, r, p, hG, early0)
        case SCon{+x, +t}:
          +early0 = Equal.trans(Bool, Nat.is_lt(String.length(w), p), Nat.is_lt(String.length(String.append(w, SNil{})), p), True{}, Equal.cong(String, Bool, z => Nat.is_lt(String.length(z), p), w, String.append(w, SNil{}), Equal.sym(String, String.append(w, SNil{}), w, slm.app_nil(w))), early)
          %Equal.sym(String, String.append(w, SNil{}), w, slm.app_nil(w)) : {slm.A(ps, ends, f, n, _, SCon{x, t}) == None{} : Maybe<&2, S.St>}
          slm.lm0(ps, ends, f, n, w, SCon{x, t}, slm.A(ps, ends, f, n, w, SCon{x, t}), {==}, slm.R(st, ps, ends, f, n, w, x, t), r, p, hG, early0)
    case SCon{+y, +u2}:
      match st:
        case S.AtStart{}:
          match m:
            case Some{+r0}:
              +h2 = slm.via(slm.A(ps, ends, f, n, w, SCon{y, String.append(u2, v)}), Some{r0}, em, String.length(w), slm.R(S.AtStart{}, ps, ends, f, n, w, y, String.append(u2, v)), Some{S.Hit{r, p}}, hG)
              slm.no_early({slm.A(ps, ends, f, n, String.append(w, SCon{y, u2}), v) == None{} : Maybe<&2, S.St>}, String.length(String.append(w, SCon{y, u2})), String.length(w), p, slm.found_p(r0, String.length(w), r, p, h2), slm.len_le(w, SCon{y, u2}), early)
            case None{}:
              +h2 = slm.via(slm.A(ps, ends, f, n, w, SCon{y, String.append(u2, v)}), None{}, em, String.length(w), slm.R(S.AtStart{}, ps, ends, f, n, w, y, String.append(u2, v)), Some{S.Hit{r, p}}, hG)
              slm.none_some({slm.A(ps, ends, f, n, String.append(w, SCon{y, u2}), v) == None{} : Maybe<&2, S.St>}, S.Hit{r, p}, h2)
        case S.Anywhere{}:
          match m:
            case Some{+r0}:
              +h2 = slm.via(slm.A(ps, ends, f, n, w, SCon{y, String.append(u2, v)}), Some{r0}, em, String.length(w), slm.R(S.Anywhere{}, ps, ends, f, n, w, y, String.append(u2, v)), Some{S.Hit{r, p}}, hG)
              slm.no_early({slm.A(ps, ends, f, n, String.append(w, SCon{y, u2}), v) == None{} : Maybe<&2, S.St>}, String.length(String.append(w, SCon{y, u2})), String.length(w), p, slm.found_p(r0, String.length(w), r, p, h2), slm.len_le(w, SCon{y, u2}), early)
            case None{}:
              +t = String.append(u2, v)
              +wy = String.append(w, SCon{y, SNil{}})
              +h2 = slm.via(slm.A(ps, ends, f, n, w, SCon{y, t}), None{}, em, String.length(w), slm.R(S.Anywhere{}, ps, ends, f, n, w, y, t), Some{S.Hit{r, p}}, hG)
              +h3 = slm.next(ps, ends, f, n, w, y, t, Some{S.Hit{r, p}}, h2)
              +early3 = Equal.trans(Bool, Nat.is_lt(String.length(String.append(wy, u2)), p), Nat.is_lt(String.length(String.append(w, SCon{y, u2})), p), True{}, Equal.cong(String, Bool, z => Nat.is_lt(String.length(z), p), String.append(wy, u2), String.append(w, SCon{y, u2}), slm.app_snoc(w, y, u2)), early)
              +rec = slm.lm(u2, S.Anywhere{}, ps, ends, f, n, wy, v, r, p, slm.A(ps, ends, f, n, wy, t), {==}, h3, early3)
              Equal.trans(Maybe<&2, S.St>, slm.A(ps, ends, f, n, String.append(w, SCon{y, u2}), v), slm.A(ps, ends, f, n, String.append(wy, u2), v), None{}, Equal.sym(Maybe<&2, S.St>, slm.A(ps, ends, f, n, String.append(wy, u2), v), slm.A(ps, ends, f, n, String.append(w, SCon{y, u2}), v), slm.A_snoc(ps, ends, f, n, w, y, u2, v)), rec)

# Fit place
# ---------

# some place after w has the answer r at char p
def slm.FP(ps: List<&2, S.Piece>, ends: Bool, f: Nat, n: Nat, w: String, v: String, r: S.St, p: Nat) -> Type:
  Sigma<&1, &1, String, a => Sigma<&1, &1, String, b => {v == String.append(a, b) : String} & ({String.length(String.append(w, a)) == p : Nat} & {slm.A(ps, ends, f, n, String.append(w, a), b) == Some{r} : Maybe<&2, S.St>})>>

# the walk answers at the first place: that place, its answer r0 = r
def slm.fp0(+ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +w: String, +v: String, +r0: S.St, em: {slm.A(ps, ends, f, n, w, v) == Some{r0} : Maybe<&2, S.St>}, +r: S.St, +p: Nat, +h2: {Some{S.Hit{r0, String.length(w)}} == Some{S.Hit{r, p}} : Maybe<&2, S.Hit>}) -> slm.FP(ps, ends, f, n, w, v, r, p):
  +e0 = slm.app_nil(w)
  +el = Equal.trans(Nat, String.length(String.append(w, SNil{})), String.length(w), p, Equal.cong(String, Nat, z => String.length(z), String.append(w, SNil{}), w, e0), slm.found_p(r0, String.length(w), r, p, h2))
  +ea = Equal.trans(Maybe<&2, S.St>, slm.A(ps, ends, f, n, String.append(w, SNil{}), v), slm.A(ps, ends, f, n, w, v), Some{r}, Equal.cong(String, Maybe<&2, S.St>, z => slm.A(ps, ends, f, n, z, v), String.append(w, SNil{}), w, e0), Equal.trans(Maybe<&2, S.St>, slm.A(ps, ends, f, n, w, v), Some{r0}, Some{r}, em, Equal.cong(S.St, Maybe<&2, S.St>, z => Some{z}, r0, r, slm.found_r(r0, String.length(w), r, p, h2))))
  (SNil{}, (v, ({==}, (el, ea))))

# the place found after w ++ [x] is a place after w, one char further in
def slm.fp_cons(+ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +w: String, +x: Char, +t: String, +r: S.St, +p: Nat, rec: slm.FP(ps, ends, f, n, String.append(w, SCon{x, SNil{}}), t, r, p)) -> slm.FP(ps, ends, f, n, w, SCon{x, t}, r, p):
  (+a, (+b, (et, (el, ea)))) = rec
  +wx = String.append(w, SCon{x, SNil{}})
  +el2 = Equal.trans(Nat, String.length(String.append(w, SCon{x, a})), String.length(String.append(wx, a)), p, Equal.cong(String, Nat, z => String.length(z), String.append(w, SCon{x, a}), String.append(wx, a), Equal.sym(String, String.append(wx, a), String.append(w, SCon{x, a}), slm.app_snoc(w, x, a))), el)
  +ea2 = Equal.trans(Maybe<&2, S.St>, slm.A(ps, ends, f, n, String.append(w, SCon{x, a}), b), slm.A(ps, ends, f, n, String.append(wx, a), b), Some{r}, Equal.sym(Maybe<&2, S.St>, slm.A(ps, ends, f, n, String.append(wx, a), b), slm.A(ps, ends, f, n, String.append(w, SCon{x, a}), b), slm.A_snoc(ps, ends, f, n, w, x, a, b)), ea)
  (SCon{x, a}, (b, (Equal.cong(String, String, z => SCon{x, z}, t, String.append(a, b), et), (el2, ea2))))

# the walk from the place after w answers r at char p: some place after w
# has that answer (m: the answer after w)
def slm.fp(v: String, +st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +w: String, +r: S.St, +p: Nat, m: Maybe<&2, S.St>, +em: {slm.A(ps, ends, f, n, w, v) == m : Maybe<&2, S.St>}, hG: {slm.G(st, ps, ends, f, n, w, v) == Some{S.Hit{r, p}} : Maybe<&2, S.Hit>}) -> slm.FP(ps, ends, f, n, w, v, r, p):
  match v:
    case SNil{}:
      match m:
        case None{}:
          +h2 = slm.via(slm.A(ps, ends, f, n, w, SNil{}), None{}, em, String.length(w), k => None{}, Some{S.Hit{r, p}}, hG)
          slm.none_some(slm.FP(ps, ends, f, n, w, SNil{}, r, p), S.Hit{r, p}, h2)
        case Some{+r0}:
          +h2 = slm.via(slm.A(ps, ends, f, n, w, SNil{}), Some{r0}, em, String.length(w), k => None{}, Some{S.Hit{r, p}}, hG)
          slm.fp0(ps, ends, f, n, w, SNil{}, r0, em, r, p, h2)
    case SCon{+x, +t}:
      match st:
        case S.AtStart{}:
          match m:
            case Some{+r0}:
              +h2 = slm.via(slm.A(ps, ends, f, n, w, SCon{x, t}), Some{r0}, em, String.length(w), slm.R(S.AtStart{}, ps, ends, f, n, w, x, t), Some{S.Hit{r, p}}, hG)
              slm.fp0(ps, ends, f, n, w, SCon{x, t}, r0, em, r, p, h2)
            case None{}:
              +h2 = slm.via(slm.A(ps, ends, f, n, w, SCon{x, t}), None{}, em, String.length(w), slm.R(S.AtStart{}, ps, ends, f, n, w, x, t), Some{S.Hit{r, p}}, hG)
              slm.none_some(slm.FP(ps, ends, f, n, w, SCon{x, t}, r, p), S.Hit{r, p}, h2)
        case S.Anywhere{}:
          match m:
            case Some{+r0}:
              +h2 = slm.via(slm.A(ps, ends, f, n, w, SCon{x, t}), Some{r0}, em, String.length(w), slm.R(S.Anywhere{}, ps, ends, f, n, w, x, t), Some{S.Hit{r, p}}, hG)
              slm.fp0(ps, ends, f, n, w, SCon{x, t}, r0, em, r, p, h2)
            case None{}:
              +wx = String.append(w, SCon{x, SNil{}})
              +h2 = slm.via(slm.A(ps, ends, f, n, w, SCon{x, t}), None{}, em, String.length(w), slm.R(S.Anywhere{}, ps, ends, f, n, w, x, t), Some{S.Hit{r, p}}, hG)
              +h3 = slm.next(ps, ends, f, n, w, x, t, Some{S.Hit{r, p}}, h2)
              slm.fp_cons(ps, ends, f, n, w, x, t, r, p, slm.fp(t, S.Anywhere{}, ps, ends, f, n, wx, r, p, slm.A(ps, ends, f, n, wx, t), {==}, h3))

# an AtStart walk answers only at its first place
def slm.at_start(v: String, +ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +w: String, +r: S.St, +p: Nat, m: Maybe<&2, S.St>, em: {slm.A(ps, ends, f, n, w, v) == m : Maybe<&2, S.St>}, hG: {slm.G(S.AtStart{}, ps, ends, f, n, w, v) == Some{S.Hit{r, p}} : Maybe<&2, S.Hit>}) -> {String.length(w) == p : Nat}:
  match v:
    case SNil{}:
      match m:
        case None{}:
          +h2 = slm.via(slm.A(ps, ends, f, n, w, SNil{}), None{}, em, String.length(w), k => None{}, Some{S.Hit{r, p}}, hG)
          slm.none_some({String.length(w) == p : Nat}, S.Hit{r, p}, h2)
        case Some{+r0}:
          +h2 = slm.via(slm.A(ps, ends, f, n, w, SNil{}), Some{r0}, em, String.length(w), k => None{}, Some{S.Hit{r, p}}, hG)
          slm.found_p(r0, String.length(w), r, p, h2)
    case SCon{+x, +t}:
      match m:
        case None{}:
          +h2 = slm.via(slm.A(ps, ends, f, n, w, SCon{x, t}), None{}, em, String.length(w), slm.R(S.AtStart{}, ps, ends, f, n, w, x, t), Some{S.Hit{r, p}}, hG)
          slm.none_some({String.length(w) == p : Nat}, S.Hit{r, p}, h2)
        case Some{+r0}:
          +h2 = slm.via(slm.A(ps, ends, f, n, w, SCon{x, t}), Some{r0}, em, String.length(w), slm.R(S.AtStart{}, ps, ends, f, n, w, x, t), Some{S.Hit{r, p}}, hG)
          slm.found_p(r0, String.length(w), r, p, h2)

# None
# ----

# the first place tested answers none when the walk answers none
def slm.nl0(v: String, +st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +w: String, m: Maybe<&2, S.St>, em: {slm.A(ps, ends, f, n, w, v) == m : Maybe<&2, S.St>}, hG: {slm.G(st, ps, ends, f, n, w, v) == None{} : Maybe<&2, S.Hit>}) -> {slm.A(ps, ends, f, n, w, v) == None{} : Maybe<&2, S.St>}:
  match v:
    case SNil{}:
      match m:
        case None{}:
          em
        case Some{+r0}:
          +h2 = slm.via(slm.A(ps, ends, f, n, w, SNil{}), Some{r0}, em, String.length(w), k => None{}, None{}, hG)
          slm.some_none({slm.A(ps, ends, f, n, w, SNil{}) == None{} : Maybe<&2, S.St>}, S.Hit{r0, String.length(w)}, h2)
    case SCon{+x, +t}:
      match m:
        case None{}:
          em
        case Some{+r0}:
          +h2 = slm.via(slm.A(ps, ends, f, n, w, SCon{x, t}), Some{r0}, em, String.length(w), slm.R(st, ps, ends, f, n, w, x, t), None{}, hG)
          slm.some_none({slm.A(ps, ends, f, n, w, SCon{x, t}) == None{} : Maybe<&2, S.St>}, S.Hit{r0, String.length(w)}, h2)

# an Anywhere walk from the place after w that answers none: no place
# after w ++ u has an answer (m: the answer after w)
def slm.nl(u: String, +ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +w: String, +v: String, m: Maybe<&2, S.St>, em: {slm.A(ps, ends, f, n, w, String.append(u, v)) == m : Maybe<&2, S.St>}, hG: {slm.G(S.Anywhere{}, ps, ends, f, n, w, String.append(u, v)) == None{} : Maybe<&2, S.Hit>}) -> {slm.A(ps, ends, f, n, String.append(w, u), v) == None{} : Maybe<&2, S.St>}:
  match u:
    case SNil{}:
      %Equal.sym(String, String.append(w, SNil{}), w, slm.app_nil(w)) : {slm.A(ps, ends, f, n, _, v) == None{} : Maybe<&2, S.St>}
      slm.nl0(v, S.Anywhere{}, ps, ends, f, n, w, m, em, hG)
    case SCon{+y, +u2}:
      match m:
        case Some{+r0}:
          +h2 = slm.via(slm.A(ps, ends, f, n, w, SCon{y, String.append(u2, v)}), Some{r0}, em, String.length(w), slm.R(S.Anywhere{}, ps, ends, f, n, w, y, String.append(u2, v)), None{}, hG)
          slm.some_none({slm.A(ps, ends, f, n, String.append(w, SCon{y, u2}), v) == None{} : Maybe<&2, S.St>}, S.Hit{r0, String.length(w)}, h2)
        case None{}:
          +t = String.append(u2, v)
          +wy = String.append(w, SCon{y, SNil{}})
          +h2 = slm.via(slm.A(ps, ends, f, n, w, SCon{y, t}), None{}, em, String.length(w), slm.R(S.Anywhere{}, ps, ends, f, n, w, y, t), None{}, hG)
          +h3 = slm.next(ps, ends, f, n, w, y, t, None{}, h2)
          +rec = slm.nl(u2, ps, ends, f, n, wy, v, slm.A(ps, ends, f, n, wy, t), {==}, h3)
          Equal.trans(Maybe<&2, S.St>, slm.A(ps, ends, f, n, String.append(w, SCon{y, u2}), v), slm.A(ps, ends, f, n, String.append(wy, u2), v), None{}, Equal.sym(Maybe<&2, S.St>, slm.A(ps, ends, f, n, String.append(wy, u2), v), slm.A(ps, ends, f, n, String.append(w, SCon{y, u2}), v), slm.A_snoc(ps, ends, f, n, w, y, u2, v)), rec)

# From `first`
# ------------

def slm.found_f(m: Maybe<&2, S.Found>, d: S.Fit) -> S.Fit:
  match m:
    case None{}:
      d
    case Some{x}:
      match x:
        case S.Found{i, fit}:
          fit

def slm.fit_at(x: S.Fit) -> Nat:
  match x:
    case S.Fit{at, to, caps}:
      at

def slm.FMIf(m: Maybe<&2, S.Found>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

def slm.fnone_some(-G: Type, -y: S.Found, e: {None{} == Some{y} : Maybe<&2, S.Found>}) -> G:
  %e : slm.FMIf(_, G)
  Unit{}

# a reading r at char p0 that spells the fit from char p
def slm.got_r(+r: S.St, +p0: Nat, +p: Nat, +q: Nat, +cs: List<&2, Maybe<&2, String>>, ef: {ShapeSearch.sp_fit(p0, r) == S.Fit{p, q, cs} : S.Fit}) -> {p0 == p : Nat}:
  match r:
    case S.St{pos, left, word, rest, caps}:
      Equal.cong(S.Fit, Nat, z => slm.fit_at(z), ShapeSearch.sp_fit(p0, S.St{pos, left, word, rest, caps}), S.Fit{p, q, cs}, ef)

# the walk's answer g spells the fit from char p: a reading at char p
def slm.got(g: Maybe<&2, S.Hit>, -G0: Maybe<&2, S.Hit>, eg: {G0 == g : Maybe<&2, S.Hit>}, +p: Nat, +q: Nat, +cs: List<&2, Maybe<&2, String>>, h: {ShapeSearch.sp_first.hit(g, 0n, k => None{}) == Some{S.Found{0n, S.Fit{p, q, cs}}} : Maybe<&2, S.Found>}) -> Sigma<&1, &1, S.St, r => {G0 == Some{S.Hit{r, p}} : Maybe<&2, S.Hit>} & {ShapeSearch.sp_fit(p, r) == S.Fit{p, q, cs} : S.Fit}>:
  match g:
    case None{}:
      slm.fnone_some(Sigma<&1, &1, S.St, r => {G0 == Some{S.Hit{r, p}} : Maybe<&2, S.Hit>} & {ShapeSearch.sp_fit(p, r) == S.Fit{p, q, cs} : S.Fit}>, S.Found{0n, S.Fit{p, q, cs}}, h)
    case Some{x}:
      match x:
        case S.Hit{+r, +p0}:
          +ef = Equal.cong(Maybe<&2, S.Found>, S.Fit, z => slm.found_f(z, S.Fit{p, q, cs}), Some{S.Found{0n, ShapeSearch.sp_fit(p0, r)}}, Some{S.Found{0n, S.Fit{p, q, cs}}}, h)
          +ep = slm.got_r(r, p0, p, q, cs, ef)
          +eg2 = Equal.trans(Maybe<&2, S.Hit>, G0, Some{S.Hit{r, p0}}, Some{S.Hit{r, p}}, eg, Equal.cong(Nat, Maybe<&2, S.Hit>, z => Some{S.Hit{r, z}}, p0, p, ep))
          +ef2 = Equal.trans(S.Fit, ShapeSearch.sp_fit(p, r), ShapeSearch.sp_fit(p0, r), S.Fit{p, q, cs}, Equal.cong(Nat, S.Fit, z => ShapeSearch.sp_fit(z, r), p, p0, Equal.sym(Nat, p0, p, ep)), ef)
          (r, (eg2, ef2))

# the walk's answer g gives no fit: none
def slm.gone(g: Maybe<&2, S.Hit>, -G0: Maybe<&2, S.Hit>, eg: {G0 == g : Maybe<&2, S.Hit>}, h: {ShapeSearch.sp_first.hit(g, 0n, k => None{}) == None{} : Maybe<&2, S.Found>}) -> {G0 == None{} : Maybe<&2, S.Hit>}:
  match g:
    case None{}:
      eg
    case Some{x}:
      match x:
        case S.Hit{+r, +p}:
          slm.fnone_some({G0 == None{} : Maybe<&2, S.Hit>}, S.Found{0n, ShapeSearch.sp_fit(p, r)}, Equal.sym(Maybe<&2, S.Found>, Some{S.Found{0n, ShapeSearch.sp_fit(p, r)}}, None{}, h))

# the walk from the text start answers at char p: the shape may start there
def slm.may(st: S.Start, +ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +text: String, +r: S.St, +p: Nat, eg: {slm.G(st, ps, ends, f, n, SNil{}, text) == Some{S.Hit{r, p}} : Maybe<&2, S.Hit>}) -> {ShapeSearch.sp_may(st, p) == True{} : Bool}:
  match st:
    case S.AtStart{}:
      +e0 = slm.at_start(text, ps, ends, f, n, SNil{}, r, p, slm.A(ps, ends, f, n, SNil{}, text), {==}, eg)
      Equal.sym(Bool, True{}, Nat.is_eq(p, 0n), Equal.cong(Nat, Bool, z => Nat.is_eq(z, 0n), 0n, p, e0))
    case S.Anywhere{}:
      {==}

# the walk from the text start answers none: no place the shape may start
# at has an answer
def slm.none_top(st: S.Start, +u: String, +ps: List<&2, S.Piece>, +ends: Bool, +f: Nat, +n: Nat, +v: String, may: {ShapeSearch.sp_may(st, String.length(u)) == True{} : Bool}, hG: {slm.G(st, ps, ends, f, n, SNil{}, String.append(u, v)) == None{} : Maybe<&2, S.Hit>}) -> {slm.A(ps, ends, f, n, u, v) == None{} : Maybe<&2, S.St>}:
  match st:
    case S.AtStart{}:
      match u:
        case SNil{}:
          slm.nl0(v, S.AtStart{}, ps, ends, f, n, SNil{}, slm.A(ps, ends, f, n, SNil{}, v), {==}, hG)
        case SCon{y, u2}:
          slm.false_true({slm.A(ps, ends, f, n, SCon{y, u2}, v) == None{} : Maybe<&2, S.St>}, may)
    case S.Anywhere{}:
      slm.nl(u, ps, ends, f, n, SNil{}, v, slm.A(ps, ends, f, n, SNil{}, String.append(u, v)), {==}, hG)
