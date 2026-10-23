# eukhe: the proof of LAW theme_mode_name_free

import Base
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../laws/theme.bend as Theme

def theme_mode_name_free(f: TFile.Th, n: String) -> {TPalette.light(TPalette.rename(f, n)) == TPalette.light(f) : Bool}:
  match f:
    case TFile.Th{name, cols, page, card, info}:
      {==}

def Theme.theme_mode_name_free(f, n):
  theme_mode_name_free(f, n)
