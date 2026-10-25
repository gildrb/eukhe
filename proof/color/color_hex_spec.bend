import Base
import ../../bend/color.bend as Co
import ../../laws/color.bend as Color
import ./color_hexd_spec.bend as PHexd

# eukhe: the proof of LAW color_hex_spec: the same seven-char shape; in it,
# each digit is the spec's (LAW color_hexd_spec) and the channels, color
# and '#' test agree (cx.join, cx.rgb, cx.sharp)

def cx.join(+b: U32, x: Maybe<&2, U32>, y: Maybe<&2, U32>) -> {Co.join(b, x, y) == Color.th.join(b, x, y) : Maybe<&2, U32>}:
  match x y:
    case None{} None{}:
      {==}
    case None{} Some{q}:
      {==}
    case Some{p} None{}:
      {==}
    case Some{p} Some{q}:
      {==}

def cx.rgb(r: Maybe<&2, U32>, g: Maybe<&2, U32>, b: Maybe<&2, U32>) -> {Co.hex.rgb(r, g, b) == Color.th.rgb3(r, g, b) : Maybe<&2, Co.Rgb>}:
  match r:
    case None{}:
      match g b:
        case None{} None{}:
          {==}
        case None{} Some{z}:
          {==}
        case Some{y} None{}:
          {==}
        case Some{y} Some{z}:
          {==}
    case Some{x}:
      match g b:
        case None{} None{}:
          {==}
        case None{} Some{z}:
          {==}
        case Some{y} None{}:
          {==}
        case Some{y} Some{z}:
          {==}

def cx.sharp(ok: Bool, m: Maybe<&2, Co.Rgb>) -> {Co.hex.sharp(ok, m) == Color.th.sharp(ok, m) : Maybe<&2, Co.Rgb>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def cx.hex7(+h: Char, +a: Char, +b: Char, +c: Char, +d: Char, +e: Char, +f: Char) -> {Co.hex(SCon{h, SCon{a, SCon{b, SCon{c, SCon{d, SCon{e, SCon{f, SNil{}}}}}}}}) == Color.th.hex7(h, a, b, c, d, e, f) : Maybe<&2, Co.Rgb>}:
  +l = Co.hex(SCon{h, SCon{a, SCon{b, SCon{c, SCon{d, SCon{e, SCon{f, SNil{}}}}}}}})
  +ok = Char.is_eq(h, '#')
  %Color.color_hexd_spec(a) : {l == Color.th.sharp(ok, Color.th.rgb3(Color.th.join(16, _, Color.th.hexv(b)), Color.th.join(16, Color.th.hexv(c), Color.th.hexv(d)), Color.th.join(16, Color.th.hexv(e), Color.th.hexv(f)))) : Maybe<&2, Co.Rgb>}
  %Color.color_hexd_spec(b) : {l == Color.th.sharp(ok, Color.th.rgb3(Color.th.join(16, Co.hexd(a), _), Color.th.join(16, Color.th.hexv(c), Color.th.hexv(d)), Color.th.join(16, Color.th.hexv(e), Color.th.hexv(f)))) : Maybe<&2, Co.Rgb>}
  %Color.color_hexd_spec(c) : {l == Color.th.sharp(ok, Color.th.rgb3(Color.th.join(16, Co.hexd(a), Co.hexd(b)), Color.th.join(16, _, Color.th.hexv(d)), Color.th.join(16, Color.th.hexv(e), Color.th.hexv(f)))) : Maybe<&2, Co.Rgb>}
  %Color.color_hexd_spec(d) : {l == Color.th.sharp(ok, Color.th.rgb3(Color.th.join(16, Co.hexd(a), Co.hexd(b)), Color.th.join(16, Co.hexd(c), _), Color.th.join(16, Color.th.hexv(e), Color.th.hexv(f)))) : Maybe<&2, Co.Rgb>}
  %Color.color_hexd_spec(e) : {l == Color.th.sharp(ok, Color.th.rgb3(Color.th.join(16, Co.hexd(a), Co.hexd(b)), Color.th.join(16, Co.hexd(c), Co.hexd(d)), Color.th.join(16, _, Color.th.hexv(f)))) : Maybe<&2, Co.Rgb>}
  %Color.color_hexd_spec(f) : {l == Color.th.sharp(ok, Color.th.rgb3(Color.th.join(16, Co.hexd(a), Co.hexd(b)), Color.th.join(16, Co.hexd(c), Co.hexd(d)), Color.th.join(16, Co.hexd(e), _))) : Maybe<&2, Co.Rgb>}
  +x = Co.hexd(a)
  +y = Co.hexd(b)
  +z = Co.hexd(c)
  +u = Co.hexd(d)
  +v = Co.hexd(e)
  +w = Co.hexd(f)
  %cx.join(16, x, y) : {l == Color.th.sharp(ok, Color.th.rgb3(_, Color.th.join(16, z, u), Color.th.join(16, v, w))) : Maybe<&2, Co.Rgb>}
  %cx.join(16, z, u) : {l == Color.th.sharp(ok, Color.th.rgb3(Co.join(16, x, y), _, Color.th.join(16, v, w))) : Maybe<&2, Co.Rgb>}
  %cx.join(16, v, w) : {l == Color.th.sharp(ok, Color.th.rgb3(Co.join(16, x, y), Co.join(16, z, u), _)) : Maybe<&2, Co.Rgb>}
  %cx.rgb(Co.join(16, x, y), Co.join(16, z, u), Co.join(16, v, w)) : {l == Color.th.sharp(ok, _) : Maybe<&2, Co.Rgb>}
  cx.sharp(ok, Co.hex.rgb(Co.join(16, x, y), Co.join(16, z, u), Co.join(16, v, w)))

def Color.color_hex_spec(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+h, s1}:
      match s1:
        case SNil{}:
          {==}
        case SCon{+a, s2}:
          match s2:
            case SNil{}:
              {==}
            case SCon{+b, s3}:
              match s3:
                case SNil{}:
                  {==}
                case SCon{+c, s4}:
                  match s4:
                    case SNil{}:
                      {==}
                    case SCon{+d, s5}:
                      match s5:
                        case SNil{}:
                          {==}
                        case SCon{+e, s6}:
                          match s6:
                            case SNil{}:
                              {==}
                            case SCon{+f, s7}:
                              match s7:
                                case SNil{}:
                                  cx.hex7(h, a, b, c, d, e, f)
                                case SCon{g, s8}:
                                  {==}
