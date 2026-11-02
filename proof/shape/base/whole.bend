# eukhe: the split of a whole list of pieces (laws/shape/match.bend R6): a split
# from no place reaches none, the end of a split, a Many's parts followed
# by more parts, and the steps of Same, the zero-width pieces and Ahead.

import Base
import ../../../bend/shape.bend as S
import ../../../laws/shape/match.bend as Shape
import ../base.bend as LA
import ./has.bend as LH
import ./fuel.bend as LU
import ./chars.bend as LQ
import ./split.bend as LP

def shn.pick_nn(took: Bool) -> {Shape.sp_pick(took, None{}, None{}) == None{} : Maybe<&2, S.St>}:
  match took:
    case True{}:
      {==}
    case False{}:
      {==}

def shn.stop_none(min: Nat) -> {Shape.sp_part_stop(min, None{}) == None{} : Maybe<&2, S.St>}:
  match min:
    case 0n:
      {==}
    case 1n+k:
      {==}

def shn.ahead_none(neg: Bool, -r: Maybe<&2, S.St>, -i: List<&2, S.Piece>, +base: Nat) -> {Shape.sp_part_ahead(neg, r, i, base, None{}) == None{} : Maybe<&2, S.St>}:
  match neg:
    case True{}:
      {==}
    case False{}:
      {==}

def shn.end_none(ps: List<&2, S.Piece>) -> {Shape.sp_split.end(ps, None{}) == None{} : Maybe<&2, S.St>}:
  match ps:
    case Nil{}:
      {==}
    case p <> t:
      {==}

# a split from no place reaches none
def shn.none(ws: List<&2, Shape.Part>, ps: List<&2, S.Piece>, +base: Nat) -> {Shape.sp_split(ws, ps, base, None{}) == None{} : Maybe<&2, S.St>}:
  match ws:
    case Nil{}:
      shn.end_none(ps)
    case w <> +wt:
      match w:
        case Shape.Part{took, +u, +wi}:
          match ps:
            case Nil{}:
              {==}
            case p <> +t:
              match p:
                case S.Lit{+v}:
                  %Equal.sym(Maybe<&2, S.St>, Shape.sp_when(Shape.sp_text_eq(False{}, u, v), None{}), None{}, LP.shp.when_none(Shape.sp_text_eq(False{}, u, v))) : {Shape.sp_split(wt, t, base, _) == None{} : Maybe<&2, S.St>}
                  shn.none(wt, t, base)
                case S.Fold{+v}:
                  %Equal.sym(Maybe<&2, S.St>, Shape.sp_when(Shape.sp_text_eq(True{}, u, v), None{}), None{}, LP.shp.when_none(Shape.sp_text_eq(True{}, u, v))) : {Shape.sp_split(wt, t, base, _) == None{} : Maybe<&2, S.St>}
                  shn.none(wt, t, base)
                case S.Run{+c, +min, +max}:
                  +b = {Bool.and(Shape.sp_all_cls(c, u), Bool.and(Nat.is_le(min, String.length(u)), Shape.sp_at_most(String.length(u), max))) : Bool}
                  %Equal.sym(Maybe<&2, S.St>, Shape.sp_when(b, None{}), None{}, LP.shp.when_none(b)) : {Shape.sp_split(wt, t, base, _) == None{} : Maybe<&2, S.St>}
                  shn.none(wt, t, base)
                case S.Cap{+i}:
                  shn.none(wt, t, 1n+Nat.add(base, Shape.sp_ncaps(i)))
                case S.Opt{+i}:
                  %Equal.sym(Maybe<&2, S.St>, Shape.sp_split(wi, i, base, None{}), None{}, shn.none(wi, i, base)) : {Shape.sp_split(wt, t, Nat.add(base, Shape.sp_ncaps(i)), Shape.sp_pick(took, _, None{})) == None{} : Maybe<&2, S.St>}
                  %Equal.sym(Maybe<&2, S.St>, Shape.sp_pick(took, None{}, None{}), None{}, shn.pick_nn(took)) : {Shape.sp_split(wt, t, Nat.add(base, Shape.sp_ncaps(i)), _) == None{} : Maybe<&2, S.St>}
                  shn.none(wt, t, Nat.add(base, Shape.sp_ncaps(i)))
                case S.Alt{+a, +bb}:
                  %Equal.sym(Maybe<&2, S.St>, Shape.sp_split(wi, a, base, None{}), None{}, shn.none(wi, a, base)) : {Shape.sp_split(wt, t, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), Shape.sp_pick(took, _, Shape.sp_split(wi, bb, Nat.add(base, Shape.sp_ncaps(a)), None{}))) == None{} : Maybe<&2, S.St>}
                  %Equal.sym(Maybe<&2, S.St>, Shape.sp_split(wi, bb, Nat.add(base, Shape.sp_ncaps(a)), None{}), None{}, shn.none(wi, bb, Nat.add(base, Shape.sp_ncaps(a)))) : {Shape.sp_split(wt, t, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), Shape.sp_pick(took, None{}, _)) == None{} : Maybe<&2, S.St>}
                  %Equal.sym(Maybe<&2, S.St>, Shape.sp_pick(took, None{}, None{}), None{}, shn.pick_nn(took)) : {Shape.sp_split(wt, t, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)), _) == None{} : Maybe<&2, S.St>}
                  shn.none(wt, t, Nat.add(Nat.add(base, Shape.sp_ncaps(a)), Shape.sp_ncaps(bb)))
                case S.Many{+i, +min}:
                  %Equal.sym(Maybe<&2, S.St>, Shape.sp_part_stop(min, None{}), None{}, shn.stop_none(min)) : {Shape.sp_pick(took, Shape.sp_split(wt, S.Many{i, Shape.sp_dec(min)} <> t, base, None{}), Shape.sp_split(wt, t, Nat.add(base, Shape.sp_ncaps(i)), _)) == None{} : Maybe<&2, S.St>}
                  %Equal.sym(Maybe<&2, S.St>, Shape.sp_split(wt, S.Many{i, Shape.sp_dec(min)} <> t, base, None{}), None{}, shn.none(wt, S.Many{i, Shape.sp_dec(min)} <> t, base)) : {Shape.sp_pick(took, _, Shape.sp_split(wt, t, Nat.add(base, Shape.sp_ncaps(i)), None{})) == None{} : Maybe<&2, S.St>}
                  %Equal.sym(Maybe<&2, S.St>, Shape.sp_split(wt, t, Nat.add(base, Shape.sp_ncaps(i)), None{}), None{}, shn.none(wt, t, Nat.add(base, Shape.sp_ncaps(i)))) : {Shape.sp_pick(took, None{}, _) == None{} : Maybe<&2, S.St>}
                  shn.pick_nn(took)
                case S.Ahead{+i, +neg}:
                  %Equal.sym(Maybe<&2, S.St>, Shape.sp_part_ahead(neg, Shape.sp_split(wi, i, base, None{}), i, base, None{}), None{}, shn.ahead_none(neg, Shape.sp_split(wi, i, base, None{}), i, base)) : {Shape.sp_split(wt, t, Nat.add(base, Shape.sp_ncaps(i)), _) == None{} : Maybe<&2, S.St>}
                  shn.none(wt, t, Nat.add(base, Shape.sp_ncaps(i)))
                case S.Same{k}:
                  shn.none(wt, t, base)
                case S.Bound{}:
                  shn.none(wt, t, base)
                case S.Begin{}:
                  shn.none(wt, t, base)
                case S.End{}:
                  shn.none(wt, t, base)

# a split some place reaches came from some place
def shn.bind(-G: Type, +wt: List<&2, Shape.Part>, +t: List<&2, S.Piece>, +b: Nat, m: Maybe<&2, S.St>, -r: S.St, h: {Shape.sp_split(wt, t, b, m) == Some{r} : Maybe<&2, S.St>}, k: @z: S.St -> {m == Some{z} : Maybe<&2, S.St>} -> {Shape.sp_split(wt, t, b, Some{z}) == Some{r} : Maybe<&2, S.St>} -> G) -> G:
  match m:
    case None{}:
      LP.shp.none_some(G, r, Equal.trans(Maybe<&2, S.St>, None{}, Shape.sp_split(wt, t, b, None{}), Some{r}, Equal.sym(Maybe<&2, S.St>, Shape.sp_split(wt, t, b, None{}), None{}, shn.none(wt, t, b)), h))
    case Some{+z}:
      k(z, {==}, h)

# a split of no pieces is no parts
def shn.end_ws(ws: List<&2, Shape.Part>, -b: Nat, -m: Maybe<&2, S.St>, -x: S.St, h: {Shape.sp_split(ws, Nil{}, b, m) == Some{x} : Maybe<&2, S.St>}) -> {ws == Nil{} : List<&2, Shape.Part>}:
  match ws:
    case Nil{}:
      {==}
    case w <> wt:
      match w:
        case Shape.Part{took, u, wi}:
          LP.shp.none_some({Shape.Part{took, u, wi} <> wt == Nil{} : List<&2, Shape.Part>}, x, h)

def shn.end_m(ws: List<&2, Shape.Part>, -b: Nat, -m: Maybe<&2, S.St>, -x: S.St, h: {Shape.sp_split(ws, Nil{}, b, m) == Some{x} : Maybe<&2, S.St>}) -> {m == Some{x} : Maybe<&2, S.St>}:
  match ws:
    case Nil{}:
      h
    case w <> wt:
      match w:
        case Shape.Part{took, u, wi}:
          LP.shp.none_some({m == Some{x} : Maybe<&2, S.St>}, x, h)

# a Many's parts, then more parts: the more parts go on from where the
# Many's parts end
def shn.many_app(ws1: List<&2, Shape.Part>, +i: List<&2, S.Piece>, +min: Nat, +t: List<&2, S.Piece>, +base: Nat, +m: Maybe<&2, S.St>, -x: S.St, +ws2: List<&2, Shape.Part>, +h: {Shape.sp_split(ws1, [S.Many{i, min}], base, m) == Some{x} : Maybe<&2, S.St>}) -> {Shape.sp_split(List.append(&2, Shape.Part, ws1, ws2), S.Many{i, min} <> t, base, m) == Shape.sp_split(ws2, t, Nat.add(base, Shape.sp_ncaps(i)), Some{x}) : Maybe<&2, S.St>}:
  match ws1:
    case Nil{}:
      LP.shp.none_some({Shape.sp_split(ws2, S.Many{i, min} <> t, base, m) == Shape.sp_split(ws2, t, Nat.add(base, Shape.sp_ncaps(i)), Some{x}) : Maybe<&2, S.St>}, x, h)
    case w <> +wt:
      match w:
        case Shape.Part{took, +u, +wi}:
          match took:
            case True{}:
              shn.many_app(wt, i, Shape.sp_dec(min), t, base, Shape.sp_part_round(m, Shape.sp_split(wi, i, base, m)), x, ws2, h)
            case False{}:
              +b2 = {Nat.add(base, Shape.sp_ncaps(i)) : Nat}
              +sm = {Shape.sp_part_stop(min, m) : Maybe<&2, S.St>}
              %Equal.sym(List<&2, Shape.Part>, wt, Nil{}, shn.end_ws(wt, b2, sm, x, h)) : {Shape.sp_split(List.append(&2, Shape.Part, _, ws2), t, b2, sm) == Shape.sp_split(ws2, t, b2, Some{x}) : Maybe<&2, S.St>}
              %Equal.sym(Maybe<&2, S.St>, sm, Some{x}, shn.end_m(wt, b2, sm, x, h)) : {Shape.sp_split(ws2, t, b2, _) == Shape.sp_split(ws2, t, b2, Some{x}) : Maybe<&2, S.St>}
              {==}

# Same
# ----

def shn.same_s(t: Maybe<&2, String>, +s: S.St, -z: S.St, h: Shape.sp_has(z, Shape.sp_same.at(t, s))) -> &u: String -> {Shape.sp_when(Shape.sp_is(t, u), Shape.sp_go_on(u, Some{s})) == Some{z} : Maybe<&2, S.St>}:
  match t:
    case None{}:
      match h:
    case Some{+v}:
      (v, Equal.trans(Maybe<&2, S.St>, Shape.sp_when(Shape.sp_text_eq(False{}, v, v), Shape.sp_go_on(v, Some{s})), Shape.sp_go_on(v, Some{s}), Some{z}, LP.shp.when_true(Shape.sp_text_eq(False{}, v, v), Shape.sp_go_on(v, Some{s}), LQ.shq.text_refl(False{}, v)), LP.shp.eat_head(v, False{}, s, z, h)))

def shn.same_c(t: Maybe<&2, String>, +u: String, +s: S.St, -z: S.St, +h: {Shape.sp_when(Shape.sp_is(t, u), Shape.sp_go_on(u, Some{s})) == Some{z} : Maybe<&2, S.St>}) -> Shape.sp_has(z, Shape.sp_same.at(t, s)):
  match t:
    case None{}:
      LP.shp.none_some(Shape.sp_has(z, Shape.sp_same.at(None{}, s)), z, h)
    case Some{+v}:
      +e = {LQ.shq.text_sound(v, u, LP.shp.when_t(Shape.sp_text_eq(False{}, v, u), Shape.sp_go_on(u, Some{s}), z, h)) : {v == u : String}}
      %Equal.sym(String, v, u, e) : Shape.sp_has(z, Shape.sp_eat(_, False{}, s))
      LP.shp.head_has(Shape.sp_eat(u, False{}, s), z, LP.shp.when_m(Shape.sp_text_eq(False{}, v, u), Shape.sp_go_on(u, Some{s}), z, h))

# Bound, Begin, End: at most one place
def shn.one_head(b: Bool, +x: S.St, -z: S.St, h: Shape.sp_has(z, Shape.sp_if(b, [x]))) -> {Shape.sp_head(Shape.sp_if(b, [x])) == Some{z} : Maybe<&2, S.St>}:
  match b:
    case True{}:
      Equal.cong(S.St, Maybe<&2, S.St>, w => Some{w}, x, z, LH.shh.single(z, x, h))
    case False{}:
      match h:

# Ahead
# -----

def shn.ahead_is(neg: Bool, xs: List<&2, S.St>, +s: S.St, -z: S.St, h: Shape.sp_has(z, Shape.sp_ahead(neg, xs, s))) -> {s == z : S.St}:
  match xs:
    case Nil{}:
      LH.shh.single(z, s, LP.shp.if_has(neg, [s], z, h))
    case x <> t:
      LH.shh.single(z, s, LP.shp.if_has(Bool.not(neg), [s], z, h))

def shn.ahead_neg(xs: List<&2, S.St>, -s: S.St, -z: S.St, h: Shape.sp_has(z, Shape.sp_ahead(True{}, xs, s))) -> {xs == Nil{} : List<&2, S.St>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match h:

def shn.ahead_pos(xs: List<&2, S.St>, -s: S.St, -z: S.St, h: Shape.sp_has(z, Shape.sp_ahead(False{}, xs, s))) -> &y: S.St -> Shape.sp_has(y, xs):
  match xs:
    case Nil{}:
      match h:
    case +x <> t:
      (x, Inl{{==}})

def shn.ahead_in(+neg: Bool, xs: List<&2, S.St>, +s: S.St, -y: S.St, h: Shape.sp_has(y, xs), e: {neg == False{} : Bool}) -> Shape.sp_has(s, Shape.sp_ahead(neg, xs, s)):
  match xs:
    case Nil{}:
      match h:
    case x <> t:
      %Equal.sym(Bool, neg, False{}, e) : Shape.sp_has(s, Shape.sp_if(Bool.not(_), [s]))
      Inl{{==}}

def shn.is_empty(xs: List<&2, S.St>, h: {List.is_empty(&2, S.St, xs) == True{} : Bool}) -> {xs == Nil{} : List<&2, S.St>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      LU.shu.absurd({x <> t == Nil{} : List<&2, S.St>}, h)

def shn.some_of(r: Maybe<&2, S.St>, -z: S.St, h: {Shape.sp_some(r) == True{} : Bool}) -> &y: S.St -> {r == Some{y} : Maybe<&2, S.St>}:
  match r:
    case None{}:
      LU.shu.absurd(&y: S.St -> {None{} == Some{y} : Maybe<&2, S.St>}, h)
    case Some{+y}:
      (y, {==})

# Many
# ----

def shn.round_m(+s: S.St, r: Maybe<&2, S.St>, -y: S.St, h: {Shape.sp_part_round(Some{s}, r) == Some{y} : Maybe<&2, S.St>}) -> {r == Some{y} : Maybe<&2, S.St>}:
  match r:
    case None{}:
      LP.shp.none_some({None{} == Some{y} : Maybe<&2, S.St>}, y, h)
    case Some{+x}:
      LP.shp.when_m(Nat.is_lt(Shape.sp_left(x), Shape.sp_left(s)), Some{x}, y, h)

def shn.round_lt(+s: S.St, r: Maybe<&2, S.St>, -y: S.St, +h: {Shape.sp_part_round(Some{s}, r) == Some{y} : Maybe<&2, S.St>}) -> {Nat.is_lt(Shape.sp_left(y), Shape.sp_left(s)) == True{} : Bool}:
  match r:
    case None{}:
      LP.shp.none_some({Nat.is_lt(Shape.sp_left(y), Shape.sp_left(s)) == True{} : Bool}, y, h)
    case Some{+x}:
      +e = {LP.shp.some_inj(x, y, LP.shp.when_m(Nat.is_lt(Shape.sp_left(x), Shape.sp_left(s)), Some{x}, y, h)) : {x == y : S.St}}
      %e : {Nat.is_lt(Shape.sp_left(_), Shape.sp_left(s)) == True{} : Bool}
      LP.shp.when_t(Nat.is_lt(Shape.sp_left(x), Shape.sp_left(s)), Some{x}, y, h)

def shn.round_in(+s: S.St, -r: Maybe<&2, S.St>, +y: S.St, e: {r == Some{y} : Maybe<&2, S.St>}, hl: {Nat.is_lt(Shape.sp_left(y), Shape.sp_left(s)) == True{} : Bool}) -> {Shape.sp_part_round(Some{s}, r) == Some{y} : Maybe<&2, S.St>}:
  %Equal.sym(Maybe<&2, S.St>, r, Some{y}, e) : {Shape.sp_part_round(Some{s}, _) == Some{y} : Maybe<&2, S.St>}
  LP.shp.when_true(Nat.is_lt(Shape.sp_left(y), Shape.sp_left(s)), Some{y}, hl)

def shn.stop_min(min: Nat, -m: Maybe<&2, S.St>, -x: S.St, h: {Shape.sp_part_stop(min, m) == Some{x} : Maybe<&2, S.St>}) -> {min == 0n : Nat}:
  match min:
    case 0n:
      {==}
    case 1n+k:
      LP.shp.none_some({1n+k == 0n : Nat}, x, h)

def shn.stop_m(min: Nat, -m: Maybe<&2, S.St>, -x: S.St, h: {Shape.sp_part_stop(min, m) == Some{x} : Maybe<&2, S.St>}) -> {m == Some{x} : Maybe<&2, S.St>}:
  match min:
    case 0n:
      h
    case 1n+k:
      LP.shp.none_some({m == Some{x} : Maybe<&2, S.St>}, x, h)

