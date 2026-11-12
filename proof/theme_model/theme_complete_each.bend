# eukhe: the proof of LAW theme_complete_each: induction on the first run

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/token.bend as TToken
import ../../bend/theme/reader.bend as TReader
import ../../bend/theme/palette.bend as TPalette
import ../../laws/theme_model.bend as ThemeModel

def tce.assoc(a: Bool, -b: Bool, -c: Bool) -> {Bool.and(a, Bool.and(b, c)) == Bool.and(Bool.and(a, b), c) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def tce.app(xs: List<&2, Maybe<&2, TFile.Val>>, +ys: List<&2, Maybe<&2, TFile.Val>>) -> {TPalette.complete(List.append(&2, Maybe<&2, TFile.Val>, xs, ys)) == Bool.and(TPalette.complete(xs), TPalette.complete(ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case Con{+m, rest}:
      %Equal.sym(Bool, TPalette.complete(List.append(&2, Maybe<&2, TFile.Val>, rest, ys)), Bool.and(TPalette.complete(rest), TPalette.complete(ys)), tce.app(rest, ys)) : {Bool.and(Maybe.is_some(&2, TFile.Val, m), _) == Bool.and(Bool.and(Maybe.is_some(&2, TFile.Val, m), TPalette.complete(rest)), TPalette.complete(ys)) : Bool}
      tce.assoc(Maybe.is_some(&2, TFile.Val, m), TPalette.complete(rest), TPalette.complete(ys))

def ThemeModel.theme_complete_each(xs, ys, v):
  (tce.app(xs, ys), {==})
