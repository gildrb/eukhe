# eukhe: the proof of LAW theme_palette_name_free

import Base
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../laws/theme.bend as Theme

def theme_palette_name_free(f: TFile.Th, n: String) -> {TPalette.palette(TPalette.rename(f, n)) == TPalette.palette(f) : List<&2, Maybe<&2, TFile.Val>>}:
  match f:
    case TFile.Th{name, cols, page, card, info}:
      {==}

def Theme.theme_palette_name_free(f, n):
  theme_palette_name_free(f, n)
