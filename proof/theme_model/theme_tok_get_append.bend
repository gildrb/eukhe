# eukhe: the proof of LAW theme_tok_get_append: induction on the first
# run; an entry's pick commutes with the fallback to the second run

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/token.bend as TToken
import ../../bend/theme/reader.bend as TReader
import ../../bend/theme/palette.bend as TPalette
import ../../laws/theme_model.bend as ThemeModel

def tga.pick(b: Bool, -v: TFile.Val, -x: Maybe<&2, TFile.Val>, -y: Maybe<&2, TFile.Val>) -> {TToken.get.pick(b, v, Maybe.or(&2, TFile.Val, x, y)) == Maybe.or(&2, TFile.Val, TToken.get.pick(b, v, x), y) : Maybe<&2, TFile.Val>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def ThemeModel.theme_tok_get_append(xs, ys, t):
  match xs:
    case Nil{}:
      {==}
    case Con{e, rest}:
      match e:
        case TFile.Ent{+k, +v}:
          %Equal.sym(Maybe<&2, TFile.Val>, TToken.get(List.append(&2, TFile.Ent, rest, ys), t), Maybe.or(&2, TFile.Val, TToken.get(rest, t), TToken.get(ys, t)), ThemeModel.theme_tok_get_append(rest, ys, t)) : {TToken.get.pick(U32.is_eq(k, t), v, _) == Maybe.or(&2, TFile.Val, TToken.get.pick(U32.is_eq(k, t), v, TToken.get(rest, t)), TToken.get(ys, t)) : Maybe<&2, TFile.Val>}
          tga.pick(U32.is_eq(k, t), v, TToken.get(rest, t), TToken.get(ys, t))
