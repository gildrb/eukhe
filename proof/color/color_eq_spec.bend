import Base
import ../../bend/color.bend as Co
import ../../laws/color.bend as Color

def Color.color_eq_spec(a, b):
  match a b:
    case Co.Rgb{ar, ag, ab} Co.Rgb{br, bg, bb}:
      {==}
