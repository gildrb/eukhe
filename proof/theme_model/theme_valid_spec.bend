# eukhe: the proof of LAW theme_valid_spec: per token, the same need by
# the same tests (vl.need), each written token the spec's (LAW
# theme_tok_get_spec); then the same fold over the same tokens

import Base
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/token.bend as TToken
import ../../spec/theme_model.bend as Tm
import ../../laws/theme_model.bend as ThemeModel
import ./theme_tok_get_spec.bend as PGet

def vl.has(+cols: List<&2, TFile.Ent>, +t: U32) -> {TToken.has(cols, t) == Tm.has(cols, t) : Bool}:
  %ThemeModel.theme_tok_get_spec(cols, t) : {Maybe.is_some(&2, TFile.Val, TToken.get(cols, t)) == Maybe.is_some(&2, TFile.Val, _) : Bool}
  {==}

def vl.need(a: Bool, b: Bool, c: Bool, d: Bool, e: Bool, +cols: List<&2, TFile.Ent>, +t: U32) -> {TToken.ok.k(TToken.kind.pick(a, b, c, d, e), cols, t) == Tm.need(a, b, c, d, e, cols, t) : Bool}:
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
              %vl.has(cols, t) : {Bool.or(TToken.has(cols, t), TToken.has(cols, 9)) == Bool.or(_, Tm.has(cols, 9)) : Bool}
              %vl.has(cols, 9) : {Bool.or(TToken.has(cols, t), TToken.has(cols, 9)) == Bool.or(TToken.has(cols, t), _) : Bool}
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
                      vl.has(cols, t)

def vl.go(+cols: List<&2, TFile.Ent>, ts: List<&2, U32>) -> {TToken.valid.go(cols, ts) == Tm.valid.go(cols, ts) : Bool}:
  match ts:
    case Nil{}:
      {==}
    case Con{+t, +rest}:
      %vl.go(cols, rest) : {Bool.and(TToken.ok(cols, t), TToken.valid.go(cols, rest)) == Bool.and(Tm.ok(cols, t), _) : Bool}
      %vl.need(U32.is_eq(t, 14), U32.is_eq(t, 15), U32.is_eq(t, 18), U32.is_eq(t, 57), U32.is_eq(t, 58), cols, t) : {Bool.and(TToken.ok(cols, t), TToken.valid.go(cols, rest)) == Bool.and(_, TToken.valid.go(cols, rest)) : Bool}
      {==}

def ThemeModel.theme_valid_spec(nm, cols, pg, cd, io):
  vl.go(cols, TToken.toks())
