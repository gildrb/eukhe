# eukhe: the proof of LAW theme_fill_map_each: induction on the first run

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/token.bend as TToken
import ../../bend/theme/reader.bend as TReader
import ../../bend/theme/palette.bend as TPalette
import ../../laws/theme_model.bend as ThemeModel

def tfm.app(+cols: List<&2, TFile.Ent>, +bg: Co.Rgb, xs: List<&2, U32>, +ys: List<&2, U32>) -> {TPalette.fill.map(cols, bg, List.append(&2, U32, xs, ys)) == List.append(&2, Maybe<&2, TFile.Val>, TPalette.fill.map(cols, bg, xs), TPalette.fill.map(cols, bg, ys)) : List<&2, Maybe<&2, TFile.Val>>}:
  match xs:
    case Nil{}:
      {==}
    case Con{+t, rest}:
      %tfm.app(cols, bg, rest, ys) : {TPalette.fill(cols, bg, t) <> TPalette.fill.map(cols, bg, List.append(&2, U32, rest, ys)) == TPalette.fill(cols, bg, t) <> _ : List<&2, Maybe<&2, TFile.Val>>}
      {==}

def ThemeModel.theme_fill_map_each(cols, bg, xs, ys, t):
  (tfm.app(cols, bg, xs, ys), {==})
