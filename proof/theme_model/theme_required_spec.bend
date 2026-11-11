# eukhe: the proof of LAW theme_required_spec: one case per test of the
# token against the five optional tokens

import Base
import ../../bend/theme/token.bend as TToken
import ../../bend/theme/reader.bend as TReader
import ../../laws/theme_model.bend as ThemeModel

def rq.go(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool) -> {TReader.required.k(TToken.kind.pick(a, b, c, d, e)) == Bool.not(Bool.or(a, Bool.or(b, Bool.or(c, Bool.or(d, e))))) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          match c:
            case True{}:
              {==}
            case False{}:
              match d:
                case True{}:
                  {==}
                case False{}:
                  match e:
                    case True{}:
                      {==}
                    case False{}:
                      {==}

def ThemeModel.theme_required_spec(t):
  rq.go(U32.is_eq(t, 14), U32.is_eq(t, 15), U32.is_eq(t, 18), U32.is_eq(t, 57), U32.is_eq(t, 58))
