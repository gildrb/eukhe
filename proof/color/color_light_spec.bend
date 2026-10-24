# eukhe: the proof of LAW color_light_spec: light compares the luminance
# the model computes, the same weighted sum of the linear channels, with
# one half

import Base
import ../../bend/color.bend as Co
import ../../laws/color.bend as Color

def Color.color_light_spec(c):
  match c:
    case Co.Rgb{r, g, b}:
      {==}
