# eukhe: the proof of LAW theme_mode_background

import Base
import ../../bend/theme.bend as T
import ../../bend/color.bend as Co
import ../../LAWS.bend as Laws

# Modes and names
# ---------------

def pt.light_bg(f: T.Th) -> {T.light(f) == Co.light(T.bg(f)) : Bool}:
  match f:
    case T.Th{name, cols, page, card, info}:
      {==}

def theme_mode_background(f: T.Th, g: T.Th, same: {T.bg(f) == T.bg(g) : Co.Rgb}) -> {T.light(f) == T.light(g) : Bool}:
  +lf = pt.light_bg(f)
  +lg = pt.light_bg(g)
  %Equal.sym(Bool, T.light(f), Co.light(T.bg(f)), lf) : {_ == T.light(g) : Bool}
  %Equal.sym(Bool, T.light(g), Co.light(T.bg(g)), lg) : {Co.light(T.bg(f)) == _ : Bool}
  Equal.cong(Co.Rgb, Bool, c => Co.light(c), T.bg(f), T.bg(g), same)

def Laws.theme_mode_background(f, g, same):
  theme_mode_background(f, g, same)
