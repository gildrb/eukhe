# eukhe: the first reading whose end condition holds is the spec's
# (shfe.first_end): `at` and the matcher's answers are read off it.

import Base
import ../../../bend/shape.bend as S
import ../../../laws/shape/match.bend as Shape

def shfe.free(xs: List<&2, S.St>) -> {S.first_end(False{}, xs) == Shape.sp_head(Shape.sp_keep(False{}, xs)) : Maybe<&2, S.St>}:
  match xs:
    case Nil{}:
      {==}
    case x <> t:
      match x:
        case S.St{pos, left, word, rest, caps}:
          {==}

def shfe.ends(xs: List<&2, S.St>) -> {S.first_end(True{}, xs) == Shape.sp_head(Shape.sp_keep(True{}, xs)) : Maybe<&2, S.St>}:
  match xs:
    case Nil{}:
      {==}
    case x <> +t:
      match x:
        case S.St{pos, left, word, rest, caps}:
          match rest:
            case SNil{}:
              {==}
            case SCon{c, r}:
              shfe.ends(t)

def shfe.first_end(e: Bool, xs: List<&2, S.St>) -> {S.first_end(e, xs) == Shape.sp_head(Shape.sp_keep(e, xs)) : Maybe<&2, S.St>}:
  match e:
    case True{}:
      shfe.ends(xs)
    case False{}:
      shfe.free(xs)
