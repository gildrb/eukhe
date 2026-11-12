# eukhe: `first` over a list of shapes, shape by shape (laws/shape/search.bend
# R8): a shape that fits no text alone is skipped with the index counted
# on, and the first that fits answers its own fit at its index.

import Base
import ../../../bend/shape.bend as S
import ../../../laws/shape/match.bend as Shape
import ../../../laws/shape/search.bend as ShapeSearch

def sfe.MIf(m: Maybe<&2, S.Found>, G: Type) -> Type:
  match m:
    case None{}:
      Unit
    case Some{x}:
      G

# None is no Some
def sfe.none_some(-G: Type, -y: S.Found, e: {None{} == Some{y} : Maybe<&2, S.Found>}) -> G:
  %e : sfe.MIf(_, G)
  Unit{}

def sfe.BIf(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def sfe.false_true(-G: Type, e: {False{} == True{} : Bool}) -> G:
  %e : sfe.BIf(_, G)
  Unit{}

def sfe.and_l(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {a == True{} : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      sfe.false_true({False{} == True{} : Bool}, e)

def sfe.and_r(a: Bool, -b: Bool, e: {Bool.and(a, b) == True{} : Bool}) -> {b == True{} : Bool}:
  match a:
    case True{}:
      e
    case False{}:
      sfe.false_true({b == True{} : Bool}, e)

def sfe.add_zero(n: Nat) -> {Nat.add(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 0n), p, sfe.add_zero(p))

def sfe.add_succ(a: Nat, -b: Nat) -> {Nat.add(a, 1n+b) == 1n+Nat.add(a, b) : Nat}:
  match a:
    case 0n:
      {==}
    case 1n+p:
      Equal.cong(Nat, Nat, z => 1n+z, Nat.add(p, 1n+b), 1n+Nat.add(p, b), sfe.add_succ(p, b))

def sfe.found_i(m: Maybe<&2, S.Found>) -> Nat:
  match m:
    case None{}:
      0n
    case Some{x}:
      match x:
        case S.Found{i, f}:
          i

def sfe.found_f(m: Maybe<&2, S.Found>, d: S.Fit) -> S.Fit:
  match m:
    case None{}:
      d
    case Some{x}:
      match x:
        case S.Found{i, f}:
          f

# a shape's search that answers no fit alone answers none
def sfe.unfit(x: Maybe<&2, S.Hit>, e: {ShapeSearch.sp_unfit(S.first.hit(x, 0n, k => None{})) == True{} : Bool}) -> {x == None{} : Maybe<&2, S.Hit>}:
  match x:
    case None{}:
      {==}
    case Some{h}:
      match h:
        case S.Hit{r, p}:
          sfe.false_true({Some{S.Hit{r, p}} == None{} : Maybe<&2, S.Hit>}, e)

# a shape that fits alone with f answers f at any index
def sfe.hit(x: Maybe<&2, S.Hit>, +i: Nat, -more: Unit -> Maybe<&2, S.Found>, +f: S.Fit, e: {S.first.hit(x, 0n, k => None{}) == Some{S.Found{0n, f}} : Maybe<&2, S.Found>}) -> {S.first.hit(x, i, more) == Some{S.Found{i, f}} : Maybe<&2, S.Found>}:
  match x:
    case None{}:
      sfe.none_some({S.first.hit(None{}, i, more) == Some{S.Found{i, f}} : Maybe<&2, S.Found>}, S.Found{0n, f}, e)
    case Some{h}:
      match h:
        case S.Hit{+r, +p}:
          +ef = Equal.cong(Maybe<&2, S.Found>, S.Fit, m => sfe.found_f(m, f), Some{S.Found{0n, S.fit(p, r)}}, Some{S.Found{0n, f}}, e)
          Equal.cong(S.Fit, Maybe<&2, S.Found>, z => Some{S.Found{i, z}}, S.fit(p, r), f, ef)

# the shapes pre fit nowhere alone, sh fits with f: first from index i
# answers f at i plus the count of pre
def sfe.go(pre: List<&2, S.Shape>, +sh: S.Shape, +post: List<&2, S.Shape>, +text: String, +i: Nat, +f: S.Fit, +none: {ShapeSearch.sp_none_fit(pre, text) == True{} : Bool}, fit: {S.first([sh], text) == Some{S.Found{0n, f}} : Maybe<&2, S.Found>}) -> {S.first.go(List.append(&2, S.Shape, pre, sh <> post), text, String.length(text), i) == Some{S.Found{Nat.add(List.length(&2, S.Shape, pre), i), f}} : Maybe<&2, S.Found>}:
  match pre:
    case Nil{}:
      sfe.hit(S.first.shape(sh, text, String.length(text)), i, k => S.first.go(post, text, String.length(text), 1n+i), f, fit)
    case +x <> +more:
      +n = String.length(text)
      +ex = sfe.unfit(S.first.shape(x, text, n), sfe.and_l(ShapeSearch.sp_unfit(S.first([x], text)), ShapeSearch.sp_none_fit(more, text), none))
      +L = List.length(&2, S.Shape, more)
      %Equal.sym(Maybe<&2, S.Hit>, S.first.shape(x, text, n), None{}, ex) : {S.first.hit(_, i, k => S.first.go(List.append(&2, S.Shape, more, sh <> post), text, n, 1n+i)) == Some{S.Found{1n+Nat.add(L, i), f}} : Maybe<&2, S.Found>}
      %sfe.add_succ(L, i) : {S.first.go(List.append(&2, S.Shape, more, sh <> post), text, n, 1n+i) == Some{S.Found{_, f}} : Maybe<&2, S.Found>}
      sfe.go(more, sh, post, text, 1n+i, f, sfe.and_r(ShapeSearch.sp_unfit(S.first([x], text)), ShapeSearch.sp_none_fit(more, text), none), fit)

# no shape fits alone: first answers none from every index
def sfe.none(shs: List<&2, S.Shape>, +text: String, +i: Nat, +none: {ShapeSearch.sp_none_fit(shs, text) == True{} : Bool}) -> {S.first.go(shs, text, String.length(text), i) == None{} : Maybe<&2, S.Found>}:
  match shs:
    case Nil{}:
      {==}
    case +x <> +more:
      +n = String.length(text)
      +ex = sfe.unfit(S.first.shape(x, text, n), sfe.and_l(ShapeSearch.sp_unfit(S.first([x], text)), ShapeSearch.sp_none_fit(more, text), none))
      %Equal.sym(Maybe<&2, S.Hit>, S.first.shape(x, text, n), None{}, ex) : {S.first.hit(_, i, k => S.first.go(more, text, n, 1n+i)) == None{} : Maybe<&2, S.Found>}
      sfe.none(more, text, 1n+i, sfe.and_r(ShapeSearch.sp_unfit(S.first([x], text)), ShapeSearch.sp_none_fit(more, text), none))
