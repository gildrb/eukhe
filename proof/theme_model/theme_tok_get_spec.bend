# eukhe: the proof of LAW theme_tok_get_spec: induction on the entries;
# the same first-hit pick

import Base
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/token.bend as TToken
import ../../spec/theme_model.bend as Tm
import ../../laws/theme_model.bend as ThemeModel

def tg.pick(hit: Bool, v: TFile.Val, o: Maybe<&2, TFile.Val>) -> {TToken.get.pick(hit, v, o) == Tm.pick_val(hit, v, o) : Maybe<&2, TFile.Val>}:
  match hit:
    case True{}:
      {==}
    case False{}:
      {==}

def ThemeModel.theme_tok_get_spec(cols, t):
  match cols:
    case Nil{}:
      {==}
    case Con{e, +rest}:
      match e:
        case TFile.Ent{+k, v}:
          %ThemeModel.theme_tok_get_spec(rest, t) : {TToken.get.pick(U32.is_eq(k, t), v, TToken.get(rest, t)) == Tm.pick_val(U32.is_eq(k, t), v, _) : Maybe<&2, TFile.Val>}
          tg.pick(U32.is_eq(k, t), v, TToken.get(rest, t))
