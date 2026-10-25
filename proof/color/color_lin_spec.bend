import Base
import ../../bend/color.bend as Co
import ../../laws/color.bend as Color
import ../../spec/color_model.bend as Cm

# eukhe: the proof of LAW color_lin_spec: the same tree and bits; the
# walks agree on every tree (cl.go)

def cl.go(t: Co.LinT, bs: List<&2, Bool>) -> {Co.lin.go(t, bs) == Cm.lgo(t, bs) : U32}:
  match t:
    case Co.Leaf{v}:
      {==}
    case Co.Node{lo, hi}:
      match bs:
        case Nil{}:
          {==}
        case Con{b, rest}:
          match b:
            case True{}:
              cl.go(hi, rest)
            case False{}:
              cl.go(lo, rest)

def Color.color_lin_spec(c):
  cl.go(Co.lin.table(), Co.bits(c))
