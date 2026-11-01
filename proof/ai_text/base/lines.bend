# eukhe: lemmas of the R5 proofs (lines): a char that is no break joins
# the first part (aitl.step); a part with no break char, then text whose
# lines start with an empty part, joins that part (aitl.app); a break read
# whole opens a new part (aitl.brk).

import Base
import ../../../bend/ai_text.bend as T
import ../../../laws/ai_text.bend as AiText
import ../../model_name/base.bend as LA

# a char that is neither `\r` nor `\n` joins the first part
def aitl.step(b13: Bool, b10: Bool, +x: Char, +t: String, h13: {b13 == False{} : Bool}, h10: {b10 == False{} : Bool}) -> {T.lines.at(Bool.and(False{}, b10), Bool.or(b13, b10), b13, x, c => T.lines.go(t, c)) == T.push(x, T.lines.go(t, False{})) : List<&2, String>}:
  match b13:
    case True{}:
      LA.mnb.absurd({T.lines.at(Bool.and(False{}, b10), Bool.or(True{}, b10), True{}, x, c => T.lines.go(t, c)) == T.push(x, T.lines.go(t, False{})) : List<&2, String>}, h13)
    case False{}:
      match b10:
        case True{}:
          LA.mnb.absurd({T.lines.at(Bool.and(False{}, True{}), Bool.or(False{}, True{}), False{}, x, c => T.lines.go(t, c)) == T.push(x, T.lines.go(t, False{})) : List<&2, String>}, h10)
        case False{}:
          {==}

# a part with no break char, then text whose lines are an empty part and
# ps: the part, then ps
def aitl.app(a: String, +y: String, -ps: List<&2, String>, ha: {AiText.sp_plain(a) == True{} : Bool}, hy: {T.lines.go(y, False{}) == "" <> ps : List<&2, String>}) -> {T.lines.go(String.append(a, y), False{}) == a <> ps : List<&2, String>}:
  match a:
    case SNil{}:
      hy
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = ha
          +u = String.append(t, y)
          +nb = LA.mnb.not_t(Bool.or(U32.is_eq(xc, 13), U32.is_eq(xc, 10)), LA.mnb.and_l(Bool.not(Bool.or(U32.is_eq(xc, 13), U32.is_eq(xc, 10))), AiText.sp_plain(t), hh))
          Equal.trans(List<&2, String>, T.lines.go(SCon{Chr{xc}, u}, False{}), T.push(Chr{xc}, T.lines.go(u, False{})), SCon{Chr{xc}, t} <> ps, aitl.step(U32.is_eq(xc, 13), U32.is_eq(xc, 10), Chr{xc}, u, LA.mnb.or_fl(U32.is_eq(xc, 13), U32.is_eq(xc, 10), nb), LA.mnb.or_fr(U32.is_eq(xc, 13), U32.is_eq(xc, 10), nb)), Equal.cong(List<&2, String>, List<&2, String>, z => T.push(Chr{xc}, z), T.lines.go(u, False{}), t <> ps, aitl.app(t, y, ps, LA.mnb.and_r(Bool.not(Bool.or(U32.is_eq(xc, 13), U32.is_eq(xc, 10))), AiText.sp_plain(t), hh), hy)))

# a text with no break char is one part
def aitl.plain(a: String, ha: {AiText.sp_plain(a) == True{} : Bool}) -> {T.lines.go(a, False{}) == [a] : List<&2, String>}:
  match a:
    case SNil{}:
      {==}
    case SCon{x, +t}:
      match x:
        case Chr{+xc}:
          +hh = ha
          +nb = LA.mnb.not_t(Bool.or(U32.is_eq(xc, 13), U32.is_eq(xc, 10)), LA.mnb.and_l(Bool.not(Bool.or(U32.is_eq(xc, 13), U32.is_eq(xc, 10))), AiText.sp_plain(t), hh))
          Equal.trans(List<&2, String>, T.lines.go(SCon{Chr{xc}, t}, False{}), T.push(Chr{xc}, T.lines.go(t, False{})), [SCon{Chr{xc}, t}], aitl.step(U32.is_eq(xc, 13), U32.is_eq(xc, 10), Chr{xc}, t, LA.mnb.or_fl(U32.is_eq(xc, 13), U32.is_eq(xc, 10), nb), LA.mnb.or_fr(U32.is_eq(xc, 13), U32.is_eq(xc, 10), nb)), Equal.cong(List<&2, String>, List<&2, String>, z => T.push(Chr{xc}, z), T.lines.go(t, False{}), [t], aitl.plain(t, LA.mnb.and_r(Bool.not(Bool.or(U32.is_eq(xc, 13), U32.is_eq(xc, 10))), AiText.sp_plain(t), hh))))

# after a `\r`, text that does not begin with `\n` reads as after no `\r`
def aitl.cr_lf(b: String, h: {AiText.sp_no_lf(b) == True{} : Bool}) -> {T.lines.go(b, True{}) == T.lines.go(b, False{}) : List<&2, String>}:
  match b:
    case SNil{}:
      {==}
    case SCon{y, +w}:
      match y:
        case Chr{+yc}:
          Equal.cong(Bool, List<&2, String>, z => T.lines.at(z, Bool.or(U32.is_eq(yc, 13), U32.is_eq(yc, 10)), U32.is_eq(yc, 13), Chr{yc}, c => T.lines.go(w, c)), U32.is_eq(yc, 10), False{}, LA.mnb.not_t(U32.is_eq(yc, 10), h))

# a break read whole opens a new part
def aitl.brk(j: Nat, +b: String, hw: {AiText.sp_whole(j, b) == True{} : Bool}) -> {T.lines.go(String.append(AiText.sp_brk(j), b), False{}) == "" <> T.lines.go(b, False{}) : List<&2, String>}:
  match j:
    case 0n:
      {==}
    case 1n:
      Equal.cong(List<&2, String>, List<&2, String>, z => "" <> z, T.lines.go(b, True{}), T.lines.go(b, False{}), aitl.cr_lf(b, hw))
    case 2n+k:
      {==}
