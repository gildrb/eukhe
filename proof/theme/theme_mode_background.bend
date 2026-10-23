# eukhe: the proof of LAW theme_mode_background

import Base
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../laws/theme.bend as Theme

# Modes and names
# ---------------

def pt.light_bg(f: TFile.Th) -> {TPalette.light(f) == Co.light(TPalette.bg(f)) : Bool}:
  match f:
    case TFile.Th{name, cols, page, card, info}:
      {==}

def theme_mode_background(f: TFile.Th, g: TFile.Th, same: {TPalette.bg(f) == TPalette.bg(g) : Co.Rgb}) -> {TPalette.light(f) == TPalette.light(g) : Bool}:
  +lf = pt.light_bg(f)
  +lg = pt.light_bg(g)
  %Equal.sym(Bool, TPalette.light(f), Co.light(TPalette.bg(f)), lf) : {_ == TPalette.light(g) : Bool}
  %Equal.sym(Bool, TPalette.light(g), Co.light(TPalette.bg(g)), lg) : {Co.light(TPalette.bg(f)) == _ : Bool}
  Equal.cong(Co.Rgb, Bool, c => Co.light(c), TPalette.bg(f), TPalette.bg(g), same)

def Theme.theme_mode_background(f, g, same):
  theme_mode_background(f, g, same)
