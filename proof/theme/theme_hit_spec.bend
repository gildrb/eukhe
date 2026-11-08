# eukhe: the proof of LAW theme_hit_spec: induction on the candidates;
# a candidate advertises n by the same valid-and-equal test

import Base
import ../../bend/theme/name.bend as TName
import ../../spec/theme/rules.bend as Ts
import ../../laws/theme.bend as Theme

def Theme.theme_hit_spec(src, n):
  match src:
    case Nil{}:
      {==}
    case Con{c, rest}:
      match c:
        case TName.Cand{nm, v, id}:
          %Theme.theme_hit_spec(rest, n) : {Bool.or(Bool.and(v, String.eq(nm, n)), TName.hit(rest, n)) == Bool.or(Bool.and(v, String.eq(nm, n)), _) : Bool}
          {==}
