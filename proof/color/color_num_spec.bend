import Base
import ../../bend/color.bend as Co
import ../../laws/color.bend as Color
import ./color_hex_spec.bend as PHex

# eukhe: the proof of LAW color_num_spec: the same one-to-three-char
# shapes; each digit, join and cap is the spec's

def cnm.digit(ok: Bool, +x: U32, +base: U32) -> {Co.digit.pick(ok, x, base) == Color.th.digit(ok, x, base) : Maybe<&2, U32>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def cnm.dec(c: Char) -> {Co.dec(c) == Color.th.decd(c) : Maybe<&2, U32>}:
  match c:
    case Chr{+x}:
      cnm.digit(Co.in(x, 48, 57), x, 48)

def cnm.lead(c: Char) -> {Co.dec.lead(c) == Color.th.decl(c) : Maybe<&2, U32>}:
  match c:
    case Chr{+x}:
      cnm.digit(Co.in(x, 49, 57), x, 48)

def cnm.cap(m: Maybe<&2, U32>) -> {Co.num.cap(m) == Color.th.cap(m) : Maybe<&2, U32>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      cnm.digit(U32.is_le(x, 255), x, 0)

def cnm.two(+a: Char, +b: Char) -> {Co.join(10, Co.dec.lead(a), Co.dec(b)) == Color.th.join(10, Color.th.decl(a), Color.th.decd(b)) : Maybe<&2, U32>}:
  %cnm.lead(a) : {Co.join(10, Co.dec.lead(a), Co.dec(b)) == Color.th.join(10, _, Color.th.decd(b)) : Maybe<&2, U32>}
  %cnm.dec(b) : {Co.join(10, Co.dec.lead(a), Co.dec(b)) == Color.th.join(10, Co.dec.lead(a), _) : Maybe<&2, U32>}
  PHex.cx.join(10, Co.dec.lead(a), Co.dec(b))

def cnm.three(+a: Char, +b: Char, +c: Char) -> {Co.num.cap(Co.join(10, Co.join(10, Co.dec.lead(a), Co.dec(b)), Co.dec(c))) == Color.th.cap(Color.th.join(10, Color.th.join(10, Color.th.decl(a), Color.th.decd(b)), Color.th.decd(c))) : Maybe<&2, U32>}:
  +l = Co.num.cap(Co.join(10, Co.join(10, Co.dec.lead(a), Co.dec(b)), Co.dec(c)))
  %cnm.two(a, b) : {l == Color.th.cap(Color.th.join(10, _, Color.th.decd(c))) : Maybe<&2, U32>}
  %cnm.dec(c) : {l == Color.th.cap(Color.th.join(10, Co.join(10, Co.dec.lead(a), Co.dec(b)), _)) : Maybe<&2, U32>}
  %PHex.cx.join(10, Co.join(10, Co.dec.lead(a), Co.dec(b)), Co.dec(c)) : {l == Color.th.cap(_) : Maybe<&2, U32>}
  cnm.cap(Co.join(10, Co.join(10, Co.dec.lead(a), Co.dec(b)), Co.dec(c)))

def Color.color_num_spec(s):
  match s:
    case SNil{}:
      {==}
    case SCon{+a, s1}:
      match s1:
        case SNil{}:
          cnm.dec(a)
        case SCon{+b, s2}:
          match s2:
            case SNil{}:
              cnm.two(a, b)
            case SCon{+c, s3}:
              match s3:
                case SNil{}:
                  cnm.three(a, b, c)
                case SCon{d, s4}:
                  {==}
