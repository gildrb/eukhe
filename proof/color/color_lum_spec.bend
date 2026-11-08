# eukhe: the proof of LAW color_lum_spec: the model's luminance is the
# same weighted sum of the linear channels

import Base
import ../../bend/color.bend as Co
import ../../laws/color/math.bend as Color

def Color.color_lum_spec(c):
  match c:
    case Co.Rgb{r, g, b}:
      {==}
