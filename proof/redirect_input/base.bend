# eukhe: lemmas of area redirect_input: each function of bend/redirect_input.bend is
# the spec helper of laws/redirect_input.bend (by the same matches, every
# inner call rewritten by its own lemma)

import Base
import ../../bend/redirect_input.bend as Ri
import ../../laws/redirect_input.bend as RedirectInput
import ../../bend/gateway_answer.bend as Ga

def rib.zero_width(+c: Char) -> {Ri.zero_width(c) == RedirectInput.ri_zero_width(c) : Bool}:
  {==}

def rib.wrapper(+c: Char) -> {Ri.wrapper(c) == RedirectInput.ri_wrapper(c) : Bool}:
  {==}

def rib.compact.at(+drop: Bool, +c: Char, +r: String) -> {Ri.compact.at(drop, c, r) == RedirectInput.ri_compact.at(drop, c, r) : String}:
  match drop:
    case True{}:
      {==}
    case False{}:
      {==}

def rib.compact(+s: String) -> {Ri.compact(s) == RedirectInput.ri_compact(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Ri.zero_width(c), RedirectInput.ri_zero_width(c), rib.zero_width(c)) : {Ri.compact.at(Bool.or(Ga.space(c), _), c, Ri.compact(t)) == RedirectInput.ri_compact.at(Bool.or(Ga.space(c), RedirectInput.ri_zero_width(c)), c, RedirectInput.ri_compact(t)) : String}
      %Equal.sym(String, Ri.compact(t), RedirectInput.ri_compact(t), rib.compact(t)) : {Ri.compact.at(Bool.or(Ga.space(c), RedirectInput.ri_zero_width(c)), c, _) == RedirectInput.ri_compact.at(Bool.or(Ga.space(c), RedirectInput.ri_zero_width(c)), c, RedirectInput.ri_compact(t)) : String}
      rib.compact.at(Bool.or(Ga.space(c), RedirectInput.ri_zero_width(c)), c, RedirectInput.ri_compact(t))

def rib.unwrap.at(+b: Bool, +c: Char, +t: String, +r: String) -> {Ri.unwrap.at(b, c, t, r) == RedirectInput.ri_unwrap.at(b, c, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rib.unwrap(+s: String) -> {Ri.unwrap(s) == RedirectInput.ri_unwrap(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Bool, Ri.wrapper(c), RedirectInput.ri_wrapper(c), rib.wrapper(c)) : {Ri.unwrap.at(_, c, t, Ri.unwrap(t)) == RedirectInput.ri_unwrap.at(RedirectInput.ri_wrapper(c), c, t, RedirectInput.ri_unwrap(t)) : String}
      %Equal.sym(String, Ri.unwrap(t), RedirectInput.ri_unwrap(t), rib.unwrap(t)) : {Ri.unwrap.at(RedirectInput.ri_wrapper(c), c, t, _) == RedirectInput.ri_unwrap.at(RedirectInput.ri_wrapper(c), c, t, RedirectInput.ri_unwrap(t)) : String}
      rib.unwrap.at(RedirectInput.ri_wrapper(c), c, t, RedirectInput.ri_unwrap(t))

def rib.clean(+s: String) -> {Ri.clean(s) == RedirectInput.ri_clean(s) : String}:
  %Equal.sym(String, Ri.compact(s), RedirectInput.ri_compact(s), rib.compact(s)) : {String.reverse(Ri.unwrap(String.reverse(Ri.unwrap(_)))) == String.reverse(RedirectInput.ri_unwrap(String.reverse(RedirectInput.ri_unwrap(RedirectInput.ri_compact(s))))) : String}
  %Equal.sym(String, Ri.unwrap(RedirectInput.ri_compact(s)), RedirectInput.ri_unwrap(RedirectInput.ri_compact(s)), rib.unwrap(RedirectInput.ri_compact(s))) : {String.reverse(Ri.unwrap(String.reverse(_))) == String.reverse(RedirectInput.ri_unwrap(String.reverse(RedirectInput.ri_unwrap(RedirectInput.ri_compact(s))))) : String}
  %Equal.sym(String, Ri.unwrap(String.reverse(RedirectInput.ri_unwrap(RedirectInput.ri_compact(s)))), RedirectInput.ri_unwrap(String.reverse(RedirectInput.ri_unwrap(RedirectInput.ri_compact(s)))), rib.unwrap(String.reverse(RedirectInput.ri_unwrap(RedirectInput.ri_compact(s))))) : {String.reverse(_) == String.reverse(RedirectInput.ri_unwrap(String.reverse(RedirectInput.ri_unwrap(RedirectInput.ri_compact(s))))) : String}
  {==}

def rib.split.at(+b: Bool, +c: Char, +t: String, +r: Maybe<&2, Ri.Cut>) -> {Ri.split.at(b, c, t, r) == RedirectInput.ri_split.at(b, c, t, r) : Maybe<&2, Ri.Cut>}:
  match b:
    case True{}:
      {==}
    case False{}:
      match r:
        case None{}:
          {==}
        case Some{+x}:
          match x:
            case Ri.Cut{+h, +u}:
              {==}

def rib.split(+s: String, +sep: Char) -> {Ri.split(s, sep) == RedirectInput.ri_split(s, sep) : Maybe<&2, Ri.Cut>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(t, sep), RedirectInput.ri_split(t, sep), rib.split(t, sep)) : {Ri.split.at(Char.is_eq(c, sep), c, t, _) == RedirectInput.ri_split.at(Char.is_eq(c, sep), c, t, RedirectInput.ri_split(t, sep)) : Maybe<&2, Ri.Cut>}
      rib.split.at(Char.is_eq(c, sep), c, t, RedirectInput.ri_split(t, sep))

def rib.scheme.at(+b: Bool, +t: String, +r: Maybe<&2, String>) -> {Ri.scheme.at(b, t, r) == RedirectInput.ri_scheme.at(b, t, r) : Maybe<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rib.scheme(+s: String) -> {Ri.scheme(s) == RedirectInput.ri_scheme(s) : Maybe<&2, String>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(Maybe<&2, String>, Ri.scheme(t), RedirectInput.ri_scheme(t), rib.scheme(t)) : {Ri.scheme.at(String.starts_with(SCon{c, t}, "://"), t, _) == RedirectInput.ri_scheme.at(String.starts_with(SCon{c, t}, "://"), t, RedirectInput.ri_scheme(t)) : Maybe<&2, String>}
      rib.scheme.at(String.starts_with(SCon{c, t}, "://"), t, RedirectInput.ri_scheme(t))

def rib.slashes.at(+b: Bool, +c: Char, +t: String, +r: String) -> {Ri.slashes.at(b, c, t, r) == RedirectInput.ri_slashes.at(b, c, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rib.slashes(+s: String) -> {Ri.slashes(s) == RedirectInput.ri_slashes(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Ri.slashes(t), RedirectInput.ri_slashes(t), rib.slashes(t)) : {Ri.slashes.at(Char.is_eq(c, '/'), c, t, _) == RedirectInput.ri_slashes.at(Char.is_eq(c, '/'), c, t, RedirectInput.ri_slashes(t)) : String}
      rib.slashes.at(Char.is_eq(c, '/'), c, t, RedirectInput.ri_slashes(t))

def rib.unslash(+s: String) -> {Ri.unslash(s) == RedirectInput.ri_unslash(s) : String}:
  %Equal.sym(String, Ri.slashes(String.reverse(s)), RedirectInput.ri_slashes(String.reverse(s)), rib.slashes(String.reverse(s))) : {String.reverse(_) == String.reverse(RedirectInput.ri_slashes(String.reverse(s))) : String}
  {==}

def rib.fragment(+m: Maybe<&2, Ri.Cut>) -> {Ri.fragment(m) == RedirectInput.ri_fragment(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ri.Cut{+h, +u}:
          {==}

def rib.hexv.at(+dec: Bool, +low: Bool, +up: Bool, +x: U32) -> {Ri.hexv.at(dec, low, up, x) == RedirectInput.ri_hexv.at(dec, low, up, x) : Maybe<&2, U32>}:
  match dec:
    case True{}:
      {==}
    case False{}:
      match low:
        case True{}:
          {==}
        case False{}:
          match up:
            case True{}:
              {==}
            case False{}:
              {==}

def rib.within(+x: U32, +lo: U32, +hi: U32) -> {Ri.within(x, lo, hi) == RedirectInput.ri_within(x, lo, hi) : Bool}:
  {==}

def rib.hexv(+c: Char) -> {Ri.hexv(c) == RedirectInput.ri_hexv(c) : Maybe<&2, U32>}:
  match c:
    case Chr{+x}:
      %Equal.sym(Bool, Ri.within(x, 48, 57), RedirectInput.ri_within(x, 48, 57), rib.within(x, 48, 57)) : {Ri.hexv.at(_, Ri.within(x, 97, 102), Ri.within(x, 65, 70), x) == RedirectInput.ri_hexv.at(RedirectInput.ri_within(x, 48, 57), RedirectInput.ri_within(x, 97, 102), RedirectInput.ri_within(x, 65, 70), x) : Maybe<&2, U32>}
      %Equal.sym(Bool, Ri.within(x, 97, 102), RedirectInput.ri_within(x, 97, 102), rib.within(x, 97, 102)) : {Ri.hexv.at(RedirectInput.ri_within(x, 48, 57), _, Ri.within(x, 65, 70), x) == RedirectInput.ri_hexv.at(RedirectInput.ri_within(x, 48, 57), RedirectInput.ri_within(x, 97, 102), RedirectInput.ri_within(x, 65, 70), x) : Maybe<&2, U32>}
      %Equal.sym(Bool, Ri.within(x, 65, 70), RedirectInput.ri_within(x, 65, 70), rib.within(x, 65, 70)) : {Ri.hexv.at(RedirectInput.ri_within(x, 48, 57), RedirectInput.ri_within(x, 97, 102), _, x) == RedirectInput.ri_hexv.at(RedirectInput.ri_within(x, 48, 57), RedirectInput.ri_within(x, 97, 102), RedirectInput.ri_within(x, 65, 70), x) : Maybe<&2, U32>}
      rib.hexv.at(RedirectInput.ri_within(x, 48, 57), RedirectInput.ri_within(x, 97, 102), RedirectInput.ri_within(x, 65, 70), x)

def rib.plain.out(+pct: Bool, +plus: Bool, +c: Char) -> {Ri.plain.out(pct, plus, c) == RedirectInput.ri_plain.out(pct, plus, c) : List<&2, Ri.Piece>}:
  match pct:
    case True{}:
      {==}
    case False{}:
      match plus:
        case True{}:
          {==}
        case False{}:
          {==}

def rib.plain.next(+pct: Bool) -> {Ri.plain.next(pct) == RedirectInput.ri_plain.next(pct) : Ri.Pct}:
  match pct:
    case True{}:
      {==}
    case False{}:
      {==}

def rib.sign.out(+m: Maybe<&2, U32>, +c: Char) -> {Ri.sign.out(m, c) == RedirectInput.ri_sign.out(m, c) : List<&2, Ri.Piece>}:
  match m:
    case None{}:
      %Equal.sym(List<&2, Ri.Piece>, Ri.plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c), RedirectInput.ri_plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c), rib.plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c)) : {Ri.UChar{'%'} <> _ == Ri.UChar{'%'} <> RedirectInput.ri_plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c) : List<&2, Ri.Piece>}
      {==}
    case Some{+v}:
      {==}

def rib.sign.next(+m: Maybe<&2, U32>, +c: Char) -> {Ri.sign.next(m, c) == RedirectInput.ri_sign.next(m, c) : Ri.Pct}:
  match m:
    case None{}:
      rib.plain.next(Char.is_eq(c, '%'))
    case Some{+v}:
      {==}

def rib.digit.out(+m: Maybe<&2, U32>, +h: Char, +v: U32, +c: Char) -> {Ri.digit.out(m, h, v, c) == RedirectInput.ri_digit.out(m, h, v, c) : List<&2, Ri.Piece>}:
  match m:
    case None{}:
      %Equal.sym(List<&2, Ri.Piece>, Ri.plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c), RedirectInput.ri_plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c), rib.plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c)) : {Ri.UChar{'%'} <> Ri.UChar{h} <> _ == Ri.UChar{'%'} <> Ri.UChar{h} <> RedirectInput.ri_plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c) : List<&2, Ri.Piece>}
      {==}
    case Some{+w}:
      {==}

def rib.digit.next(+m: Maybe<&2, U32>, +c: Char) -> {Ri.digit.next(m, c) == RedirectInput.ri_digit.next(m, c) : Ri.Pct}:
  match m:
    case None{}:
      rib.plain.next(Char.is_eq(c, '%'))
    case Some{+w}:
      {==}

def rib.pout(+st: Ri.Pct, +c: Char) -> {Ri.pout(st, c) == RedirectInput.ri_pout(st, c) : List<&2, Ri.Piece>}:
  match st:
    case Ri.PPlain{}:
      rib.plain.out(Char.is_eq(c, '%'), Char.is_eq(c, '+'), c)
    case Ri.PSign{}:
      %Equal.sym(Maybe<&2, U32>, Ri.hexv(c), RedirectInput.ri_hexv(c), rib.hexv(c)) : {Ri.sign.out(_, c) == RedirectInput.ri_sign.out(RedirectInput.ri_hexv(c), c) : List<&2, Ri.Piece>}
      rib.sign.out(RedirectInput.ri_hexv(c), c)
    case Ri.PDigit{+h, +v}:
      %Equal.sym(Maybe<&2, U32>, Ri.hexv(c), RedirectInput.ri_hexv(c), rib.hexv(c)) : {Ri.digit.out(_, h, v, c) == RedirectInput.ri_digit.out(RedirectInput.ri_hexv(c), h, v, c) : List<&2, Ri.Piece>}
      rib.digit.out(RedirectInput.ri_hexv(c), h, v, c)

def rib.pnext(+st: Ri.Pct, +c: Char) -> {Ri.pnext(st, c) == RedirectInput.ri_pnext(st, c) : Ri.Pct}:
  match st:
    case Ri.PPlain{}:
      rib.plain.next(Char.is_eq(c, '%'))
    case Ri.PSign{}:
      %Equal.sym(Maybe<&2, U32>, Ri.hexv(c), RedirectInput.ri_hexv(c), rib.hexv(c)) : {Ri.sign.next(_, c) == RedirectInput.ri_sign.next(RedirectInput.ri_hexv(c), c) : Ri.Pct}
      rib.sign.next(RedirectInput.ri_hexv(c), c)
    case Ri.PDigit{+h, +v}:
      %Equal.sym(Maybe<&2, U32>, Ri.hexv(c), RedirectInput.ri_hexv(c), rib.hexv(c)) : {Ri.digit.next(_, c) == RedirectInput.ri_digit.next(RedirectInput.ri_hexv(c), c) : Ri.Pct}
      rib.digit.next(RedirectInput.ri_hexv(c), c)

def rib.pend(+st: Ri.Pct) -> {Ri.pend(st) == RedirectInput.ri_pend(st) : List<&2, Ri.Piece>}:
  match st:
    case Ri.PPlain{}:
      {==}
    case Ri.PSign{}:
      {==}
    case Ri.PDigit{+h, +v}:
      {==}

def rib.units(+s: String, +st: Ri.Pct) -> {Ri.units(s, st) == RedirectInput.ri_units(s, st) : List<&2, Ri.Piece>}:
  match s:
    case SNil{}:
      rib.pend(st)
    case SCon{+c, +t}:
      %Equal.sym(List<&2, Ri.Piece>, Ri.pout(st, c), RedirectInput.ri_pout(st, c), rib.pout(st, c)) : {List.append(&2, Ri.Piece, _, Ri.units(t, Ri.pnext(st, c))) == List.append(&2, Ri.Piece, RedirectInput.ri_pout(st, c), RedirectInput.ri_units(t, RedirectInput.ri_pnext(st, c))) : List<&2, Ri.Piece>}
      %Equal.sym(Ri.Pct, Ri.pnext(st, c), RedirectInput.ri_pnext(st, c), rib.pnext(st, c)) : {List.append(&2, Ri.Piece, RedirectInput.ri_pout(st, c), Ri.units(t, _)) == List.append(&2, Ri.Piece, RedirectInput.ri_pout(st, c), RedirectInput.ri_units(t, RedirectInput.ri_pnext(st, c))) : List<&2, Ri.Piece>}
      %Equal.sym(List<&2, Ri.Piece>, Ri.units(t, RedirectInput.ri_pnext(st, c)), RedirectInput.ri_units(t, RedirectInput.ri_pnext(st, c)), rib.units(t, RedirectInput.ri_pnext(st, c))) : {List.append(&2, Ri.Piece, RedirectInput.ri_pout(st, c), _) == List.append(&2, Ri.Piece, RedirectInput.ri_pout(st, c), RedirectInput.ri_units(t, RedirectInput.ri_pnext(st, c))) : List<&2, Ri.Piece>}
      {==}

def rib.bad() -> {Ri.bad() == RedirectInput.ri_bad() : Char}:
  {==}

def rib.lead.four.at(+f0: Bool, +f1: Bool, +f4: Bool, +b: U32) -> {Ri.lead.four.at(f0, f1, f4, b) == RedirectInput.ri_lead.four.at(f0, f1, f4, b) : Ri.UStep}:
  match f0:
    case True{}:
      {==}
    case False{}:
      match f1:
        case True{}:
          {==}
        case False{}:
          match f4:
            case True{}:
              {==}
            case False{}:
              %Equal.sym(Char, Ri.bad(), RedirectInput.ri_bad(), rib.bad()) : {Ri.UStep{SCon{_, SNil{}}, Ri.UIdle{}} == Ri.UStep{SCon{RedirectInput.ri_bad(), SNil{}}, Ri.UIdle{}} : Ri.UStep}
              {==}

def rib.lead.four(+b: U32) -> {Ri.lead.four(b) == RedirectInput.ri_lead.four(b) : Ri.UStep}:
  %Equal.sym(Bool, Ri.within(b, 241, 243), RedirectInput.ri_within(b, 241, 243), rib.within(b, 241, 243)) : {Ri.lead.four.at(U32.is_eq(b, 240), _, U32.is_eq(b, 244), b) == RedirectInput.ri_lead.four.at(U32.is_eq(b, 240), RedirectInput.ri_within(b, 241, 243), U32.is_eq(b, 244), b) : Ri.UStep}
  rib.lead.four.at(U32.is_eq(b, 240), RedirectInput.ri_within(b, 241, 243), U32.is_eq(b, 244), b)

def rib.lead.three.at(+e0: Bool, +ed: Bool, +e1: Bool, +b: U32) -> {Ri.lead.three.at(e0, ed, e1, b) == RedirectInput.ri_lead.three.at(e0, ed, e1, b) : Ri.UStep}:
  match e0:
    case True{}:
      {==}
    case False{}:
      match ed:
        case True{}:
          {==}
        case False{}:
          match e1:
            case True{}:
              {==}
            case False{}:
              rib.lead.four(b)

def rib.lead.three(+b: U32) -> {Ri.lead.three(b) == RedirectInput.ri_lead.three(b) : Ri.UStep}:
  %Equal.sym(Bool, Ri.within(b, 225, 239), RedirectInput.ri_within(b, 225, 239), rib.within(b, 225, 239)) : {Ri.lead.three.at(U32.is_eq(b, 224), U32.is_eq(b, 237), _, b) == RedirectInput.ri_lead.three.at(U32.is_eq(b, 224), U32.is_eq(b, 237), RedirectInput.ri_within(b, 225, 239), b) : Ri.UStep}
  rib.lead.three.at(U32.is_eq(b, 224), U32.is_eq(b, 237), RedirectInput.ri_within(b, 225, 239), b)

def rib.lead.at(+ascii: Bool, +two: Bool, +b: U32) -> {Ri.lead.at(ascii, two, b) == RedirectInput.ri_lead.at(ascii, two, b) : Ri.UStep}:
  match ascii:
    case True{}:
      {==}
    case False{}:
      match two:
        case True{}:
          {==}
        case False{}:
          rib.lead.three(b)

def rib.lead(+b: U32) -> {Ri.lead(b) == RedirectInput.ri_lead(b) : Ri.UStep}:
  %Equal.sym(Bool, Ri.within(b, 194, 223), RedirectInput.ri_within(b, 194, 223), rib.within(b, 194, 223)) : {Ri.lead.at(U32.is_lt(b, 128), _, b) == RedirectInput.ri_lead.at(U32.is_lt(b, 128), RedirectInput.ri_within(b, 194, 223), b) : Ri.UStep}
  rib.lead.at(U32.is_lt(b, 128), RedirectInput.ri_within(b, 194, 223), b)

def rib.cont.at(+more: Nat, +v: U32) -> {Ri.cont.at(more, v) == RedirectInput.ri_cont.at(more, v) : Ri.UStep}:
  match more:
    case 0n:
      {==}
    case 1n++m:
      {==}

def rib.broken(+s: Ri.UStep) -> {Ri.broken(s) == RedirectInput.ri_broken(s) : Ri.UStep}:
  match s:
    case Ri.UStep{+o, +n}:
      %Equal.sym(Char, Ri.bad(), RedirectInput.ri_bad(), rib.bad()) : {Ri.UStep{SCon{_, o}, n} == Ri.UStep{SCon{RedirectInput.ri_bad(), o}, n} : Ri.UStep}
      {==}

def rib.cont(+ok: Bool, +more: Nat, +acc: U32, +b: U32) -> {Ri.cont(ok, more, acc, b) == RedirectInput.ri_cont(ok, more, acc, b) : Ri.UStep}:
  match ok:
    case True{}:
      rib.cont.at(more, U32.add(U32.mul(acc, 64), U32.sub(b, 128)))
    case False{}:
      %Equal.sym(Ri.UStep, Ri.lead(b), RedirectInput.ri_lead(b), rib.lead(b)) : {Ri.broken(_) == RedirectInput.ri_broken(RedirectInput.ri_lead(b)) : Ri.UStep}
      rib.broken(RedirectInput.ri_lead(b))

def rib.ustep(+st: Ri.Utf, +u: Ri.Piece) -> {Ri.ustep(st, u) == RedirectInput.ri_ustep(st, u) : Ri.UStep}:
  match st:
    case Ri.UIdle{}:
      match u:
        case Ri.UChar{+c}:
          {==}
        case Ri.UByte{+b}:
          rib.lead(b)
    case Ri.UNeed{+more, +acc, +lo, +hi}:
      match u:
        case Ri.UChar{+c}:
          %Equal.sym(Char, Ri.bad(), RedirectInput.ri_bad(), rib.bad()) : {Ri.UStep{SCon{_, SCon{c, SNil{}}}, Ri.UIdle{}} == Ri.UStep{SCon{RedirectInput.ri_bad(), SCon{c, SNil{}}}, Ri.UIdle{}} : Ri.UStep}
          {==}
        case Ri.UByte{+b}:
          %Equal.sym(Bool, Ri.within(b, lo, hi), RedirectInput.ri_within(b, lo, hi), rib.within(b, lo, hi)) : {Ri.cont(_, more, acc, b) == RedirectInput.ri_cont(RedirectInput.ri_within(b, lo, hi), more, acc, b) : Ri.UStep}
          rib.cont(RedirectInput.ri_within(b, lo, hi), more, acc, b)

def rib.uend(+st: Ri.Utf) -> {Ri.uend(st) == RedirectInput.ri_uend(st) : String}:
  match st:
    case Ri.UIdle{}:
      {==}
    case Ri.UNeed{+more, +acc, +lo, +hi}:
      %Equal.sym(Char, Ri.bad(), RedirectInput.ri_bad(), rib.bad()) : {SCon{_, SNil{}} == SCon{RedirectInput.ri_bad(), SNil{}} : String}
      {==}

def rib.uout(+s: Ri.UStep) -> {Ri.uout(s) == RedirectInput.ri_uout(s) : String}:
  match s:
    case Ri.UStep{+o, +n}:
      {==}

def rib.unext(+s: Ri.UStep) -> {Ri.unext(s) == RedirectInput.ri_unext(s) : Ri.Utf}:
  match s:
    case Ri.UStep{+o, +n}:
      {==}

def rib.utf(+us: List<&2, Ri.Piece>, +st: Ri.Utf) -> {Ri.utf(us, st) == RedirectInput.ri_utf(us, st) : String}:
  match us:
    case Nil{}:
      rib.uend(st)
    case +u <> +rest:
      %Equal.sym(Ri.UStep, Ri.ustep(st, u), RedirectInput.ri_ustep(st, u), rib.ustep(st, u)) : {String.append(Ri.uout(_), Ri.utf(rest, Ri.unext(Ri.ustep(st, u)))) == String.append(RedirectInput.ri_uout(RedirectInput.ri_ustep(st, u)), RedirectInput.ri_utf(rest, RedirectInput.ri_unext(RedirectInput.ri_ustep(st, u)))) : String}
      %Equal.sym(String, Ri.uout(RedirectInput.ri_ustep(st, u)), RedirectInput.ri_uout(RedirectInput.ri_ustep(st, u)), rib.uout(RedirectInput.ri_ustep(st, u))) : {String.append(_, Ri.utf(rest, Ri.unext(Ri.ustep(st, u)))) == String.append(RedirectInput.ri_uout(RedirectInput.ri_ustep(st, u)), RedirectInput.ri_utf(rest, RedirectInput.ri_unext(RedirectInput.ri_ustep(st, u)))) : String}
      %Equal.sym(Ri.UStep, Ri.ustep(st, u), RedirectInput.ri_ustep(st, u), rib.ustep(st, u)) : {String.append(RedirectInput.ri_uout(RedirectInput.ri_ustep(st, u)), Ri.utf(rest, Ri.unext(_))) == String.append(RedirectInput.ri_uout(RedirectInput.ri_ustep(st, u)), RedirectInput.ri_utf(rest, RedirectInput.ri_unext(RedirectInput.ri_ustep(st, u)))) : String}
      %Equal.sym(Ri.Utf, Ri.unext(RedirectInput.ri_ustep(st, u)), RedirectInput.ri_unext(RedirectInput.ri_ustep(st, u)), rib.unext(RedirectInput.ri_ustep(st, u))) : {String.append(RedirectInput.ri_uout(RedirectInput.ri_ustep(st, u)), Ri.utf(rest, _)) == String.append(RedirectInput.ri_uout(RedirectInput.ri_ustep(st, u)), RedirectInput.ri_utf(rest, RedirectInput.ri_unext(RedirectInput.ri_ustep(st, u)))) : String}
      %Equal.sym(String, Ri.utf(rest, RedirectInput.ri_unext(RedirectInput.ri_ustep(st, u))), RedirectInput.ri_utf(rest, RedirectInput.ri_unext(RedirectInput.ri_ustep(st, u))), rib.utf(rest, RedirectInput.ri_unext(RedirectInput.ri_ustep(st, u)))) : {String.append(RedirectInput.ri_uout(RedirectInput.ri_ustep(st, u)), _) == String.append(RedirectInput.ri_uout(RedirectInput.ri_ustep(st, u)), RedirectInput.ri_utf(rest, RedirectInput.ri_unext(RedirectInput.ri_ustep(st, u)))) : String}
      {==}

def rib.decode(+s: String) -> {Ri.decode(s) == RedirectInput.ri_decode(s) : String}:
  %Equal.sym(List<&2, Ri.Piece>, Ri.units(s, Ri.PPlain{}), RedirectInput.ri_units(s, Ri.PPlain{}), rib.units(s, Ri.PPlain{})) : {Ri.utf(_, Ri.UIdle{}) == RedirectInput.ri_utf(RedirectInput.ri_units(s, Ri.PPlain{}), Ri.UIdle{}) : String}
  rib.utf(RedirectInput.ri_units(s, Ri.PPlain{}), Ri.UIdle{})

def rib.param(+m: Maybe<&2, Ri.Cut>, +s: String) -> {Ri.param(m, s) == RedirectInput.ri_param(m, s) : Ri.Param}:
  match m:
    case None{}:
      %Equal.sym(String, Ri.decode(s), RedirectInput.ri_decode(s), rib.decode(s)) : {Ri.Param{_, SNil{}} == Ri.Param{RedirectInput.ri_decode(s), SNil{}} : Ri.Param}
      {==}
    case Some{+x}:
      match x:
        case Ri.Cut{+h, +u}:
          %Equal.sym(String, Ri.decode(h), RedirectInput.ri_decode(h), rib.decode(h)) : {Ri.Param{_, Ri.decode(u)} == Ri.Param{RedirectInput.ri_decode(h), RedirectInput.ri_decode(u)} : Ri.Param}
          %Equal.sym(String, Ri.decode(u), RedirectInput.ri_decode(u), rib.decode(u)) : {Ri.Param{RedirectInput.ri_decode(h), _} == Ri.Param{RedirectInput.ri_decode(h), RedirectInput.ri_decode(u)} : Ri.Param}
          {==}

def rib.params.at(+empty: Bool, +p: String, +r: List<&2, Ri.Param>) -> {Ri.params.at(empty, p, r) == RedirectInput.ri_params.at(empty, p, r) : List<&2, Ri.Param>}:
  match empty:
    case True{}:
      {==}
    case False{}:
      %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(p, '='), RedirectInput.ri_split(p, '='), rib.split(p, '=')) : {Ri.param(_, p) <> r == RedirectInput.ri_param(RedirectInput.ri_split(p, '='), p) <> r : List<&2, Ri.Param>}
      %Equal.sym(Ri.Param, Ri.param(RedirectInput.ri_split(p, '='), p), RedirectInput.ri_param(RedirectInput.ri_split(p, '='), p), rib.param(RedirectInput.ri_split(p, '='), p)) : {_ <> r == RedirectInput.ri_param(RedirectInput.ri_split(p, '='), p) <> r : List<&2, Ri.Param>}
      {==}

def rib.params.go(+ps: List<&2, String>) -> {Ri.params.go(ps) == RedirectInput.ri_params.go(ps) : List<&2, Ri.Param>}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      %Equal.sym(List<&2, Ri.Param>, Ri.params.go(rest), RedirectInput.ri_params.go(rest), rib.params.go(rest)) : {Ri.params.at(String.is_empty(p), p, _) == RedirectInput.ri_params.at(String.is_empty(p), p, RedirectInput.ri_params.go(rest)) : List<&2, Ri.Param>}
      rib.params.at(String.is_empty(p), p, RedirectInput.ri_params.go(rest))

def rib.params(+s: String) -> {Ri.params(s) == RedirectInput.ri_params(s) : List<&2, Ri.Param>}:
  rib.params.go(String.split(s, '&'))

def rib.find.at(+b: Bool, +v: String, +r: Maybe<&2, String>) -> {Ri.find.at(b, v, r) == RedirectInput.ri_find.at(b, v, r) : Maybe<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rib.find(+name: String, +ps: List<&2, Ri.Param>) -> {Ri.find(name, ps) == RedirectInput.ri_find(name, ps) : Maybe<&2, String>}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      match p:
        case Ri.Param{+n, +v}:
          %Equal.sym(Maybe<&2, String>, Ri.find(name, rest), RedirectInput.ri_find(name, rest), rib.find(name, rest)) : {Ri.find.at(Bool.and(String.eq(n, name), Bool.not(String.is_empty(v))), v, _) == RedirectInput.ri_find.at(Bool.and(String.eq(n, name), Bool.not(String.is_empty(v))), v, RedirectInput.ri_find(name, rest)) : Maybe<&2, String>}
          rib.find.at(Bool.and(String.eq(n, name), Bool.not(String.is_empty(v))), v, RedirectInput.ri_find(name, rest))

def rib.get.at(+m: Maybe<&2, String>, +r: Maybe<&2, String>) -> {Ri.get.at(m, r) == RedirectInput.ri_get.at(m, r) : Maybe<&2, String>}:
  match m:
    case None{}:
      {==}
    case Some{+v}:
      {==}

def rib.get(+name: String, +cs: List<&2, String>) -> {Ri.get(name, cs) == RedirectInput.ri_get(name, cs) : Maybe<&2, String>}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +rest:
      %Equal.sym(List<&2, Ri.Param>, Ri.params(c), RedirectInput.ri_params(c), rib.params(c)) : {Ri.get.at(Ri.find(name, _), Ri.get(name, rest)) == RedirectInput.ri_get.at(RedirectInput.ri_find(name, RedirectInput.ri_params(c)), RedirectInput.ri_get(name, rest)) : Maybe<&2, String>}
      %Equal.sym(Maybe<&2, String>, Ri.find(name, RedirectInput.ri_params(c)), RedirectInput.ri_find(name, RedirectInput.ri_params(c)), rib.find(name, RedirectInput.ri_params(c))) : {Ri.get.at(_, Ri.get(name, rest)) == RedirectInput.ri_get.at(RedirectInput.ri_find(name, RedirectInput.ri_params(c)), RedirectInput.ri_get(name, rest)) : Maybe<&2, String>}
      %Equal.sym(Maybe<&2, String>, Ri.get(name, rest), RedirectInput.ri_get(name, rest), rib.get(name, rest)) : {Ri.get.at(RedirectInput.ri_find(name, RedirectInput.ri_params(c)), _) == RedirectInput.ri_get.at(RedirectInput.ri_find(name, RedirectInput.ri_params(c)), RedirectInput.ri_get(name, rest)) : Maybe<&2, String>}
      rib.get.at(RedirectInput.ri_find(name, RedirectInput.ri_params(c)), RedirectInput.ri_get(name, rest))

def rib.from_code(+m: Maybe<&2, String>, +cs: List<&2, String>) -> {Ri.from_code(m, cs) == RedirectInput.ri_from_code(m, cs) : Ri.Answer}:
  match m:
    case None{}:
      {==}
    case Some{+c}:
      %Equal.sym(Maybe<&2, String>, Ri.get("state", cs), RedirectInput.ri_get("state", cs), rib.get("state", cs)) : {Ri.Pasted{c, _} == Ri.Pasted{c, RedirectInput.ri_get("state", cs)} : Ri.Answer}
      {==}

def rib.from_error(+m: Maybe<&2, String>, +cs: List<&2, String>) -> {Ri.from_error(m, cs) == RedirectInput.ri_from_error(m, cs) : Ri.Answer}:
  match m:
    case Some{+e}:
      %Equal.sym(Maybe<&2, String>, Ri.get("error_description", cs), RedirectInput.ri_get("error_description", cs), rib.get("error_description", cs)) : {Ri.Failed{Ri.FProvider{e, _}} == Ri.Failed{Ri.FProvider{e, RedirectInput.ri_get("error_description", cs)}} : Ri.Answer}
      {==}
    case None{}:
      %Equal.sym(Maybe<&2, String>, Ri.get("code", cs), RedirectInput.ri_get("code", cs), rib.get("code", cs)) : {Ri.from_code(_, cs) == RedirectInput.ri_from_code(RedirectInput.ri_get("code", cs), cs) : Ri.Answer}
      rib.from_code(RedirectInput.ri_get("code", cs), cs)

def rib.from_params(+cs: List<&2, String>) -> {Ri.from_params(cs) == RedirectInput.ri_from_params(cs) : Ri.Answer}:
  %Equal.sym(Maybe<&2, String>, Ri.get("error", cs), RedirectInput.ri_get("error", cs), rib.get("error", cs)) : {Ri.from_error(_, cs) == RedirectInput.ri_from_error(RedirectInput.ri_get("error", cs), cs) : Ri.Answer}
  rib.from_error(RedirectInput.ri_get("error", cs), cs)

def rib.key(+m: Maybe<&2, Ri.Cut>) -> {Ri.key(m) == RedirectInput.ri_key(m) : Bool}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      match x:
        case Ri.Cut{+h, +u}:
          {==}

def rib.carries.go(+ps: List<&2, String>) -> {Ri.carries.go(ps) == RedirectInput.ri_carries.go(ps) : Bool}:
  match ps:
    case Nil{}:
      {==}
    case +p <> +rest:
      %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(p, '='), RedirectInput.ri_split(p, '='), rib.split(p, '=')) : {Bool.or(Ri.key(_), Ri.carries.go(rest)) == Bool.or(RedirectInput.ri_key(RedirectInput.ri_split(p, '=')), RedirectInput.ri_carries.go(rest)) : Bool}
      %Equal.sym(Bool, Ri.key(RedirectInput.ri_split(p, '=')), RedirectInput.ri_key(RedirectInput.ri_split(p, '=')), rib.key(RedirectInput.ri_split(p, '='))) : {Bool.or(_, Ri.carries.go(rest)) == Bool.or(RedirectInput.ri_key(RedirectInput.ri_split(p, '=')), RedirectInput.ri_carries.go(rest)) : Bool}
      %Equal.sym(Bool, Ri.carries.go(rest), RedirectInput.ri_carries.go(rest), rib.carries.go(rest)) : {Bool.or(RedirectInput.ri_key(RedirectInput.ri_split(p, '=')), _) == Bool.or(RedirectInput.ri_key(RedirectInput.ri_split(p, '=')), RedirectInput.ri_carries.go(rest)) : Bool}
      {==}

def rib.carries(+s: String) -> {Ri.carries(s) == RedirectInput.ri_carries(s) : Bool}:
  rib.carries.go(String.split(s, '&'))

def rib.bare.state(+empty: Bool, +f: String) -> {Ri.bare.state(empty, f) == RedirectInput.ri_bare.state(empty, f) : Maybe<&2, String>}:
  match empty:
    case True{}:
      {==}
    case False{}:
      {==}

def rib.bare.at(+in_head: Bool, +in_frag: Bool, +empty: Bool, +h: String, +f: String) -> {Ri.bare.at(in_head, in_frag, empty, h, f) == RedirectInput.ri_bare.at(in_head, in_frag, empty, h, f) : Ri.Answer}:
  match in_head:
    case True{}:
      %Equal.sym(String, Ri.unslash(h), RedirectInput.ri_unslash(h), rib.unslash(h)) : {Ri.from_params([_]) == RedirectInput.ri_from_params([RedirectInput.ri_unslash(h)]) : Ri.Answer}
      rib.from_params([RedirectInput.ri_unslash(h)])
    case False{}:
      match in_frag:
        case True{}:
          rib.from_params([f])
        case False{}:
          match empty:
            case True{}:
              {==}
            case False{}:
              %Equal.sym(Maybe<&2, String>, Ri.bare.state(String.is_empty(f), f), RedirectInput.ri_bare.state(String.is_empty(f), f), rib.bare.state(String.is_empty(f), f)) : {Ri.Pasted{h, _} == Ri.Pasted{h, RedirectInput.ri_bare.state(String.is_empty(f), f)} : Ri.Answer}
              {==}

def rib.bare(+h: String, +f: String) -> {Ri.bare(h, f) == RedirectInput.ri_bare(h, f) : Ri.Answer}:
  %Equal.sym(Bool, Ri.carries(h), RedirectInput.ri_carries(h), rib.carries(h)) : {Ri.bare.at(_, Ri.carries(f), String.is_empty(h), h, f) == RedirectInput.ri_bare.at(RedirectInput.ri_carries(h), RedirectInput.ri_carries(f), String.is_empty(h), h, f) : Ri.Answer}
  %Equal.sym(Bool, Ri.carries(f), RedirectInput.ri_carries(f), rib.carries(f)) : {Ri.bare.at(RedirectInput.ri_carries(h), _, String.is_empty(h), h, f) == RedirectInput.ri_bare.at(RedirectInput.ri_carries(h), RedirectInput.ri_carries(f), String.is_empty(h), h, f) : Ri.Answer}
  rib.bare.at(RedirectInput.ri_carries(h), RedirectInput.ri_carries(f), String.is_empty(h), h, f)

def rib.parse.hash(+m: Maybe<&2, Ri.Cut>, +v: String) -> {Ri.parse.hash(m, v) == RedirectInput.ri_parse.hash(m, v) : Ri.Answer}:
  match m:
    case None{}:
      rib.bare(v, SNil{})
    case Some{+x}:
      match x:
        case Ri.Cut{+h, +f}:
          rib.bare(h, f)

def rib.parse.scheme(+m: Maybe<&2, String>, +v: String) -> {Ri.parse.scheme(m, v) == RedirectInput.ri_parse.scheme(m, v) : Ri.Answer}:
  match m:
    case Some{+rest}:
      %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(rest, '#'), RedirectInput.ri_split(rest, '#'), rib.split(rest, '#')) : {Ri.from_params([Ri.fragment(_)]) == RedirectInput.ri_from_params([RedirectInput.ri_fragment(RedirectInput.ri_split(rest, '#'))]) : Ri.Answer}
      %Equal.sym(String, Ri.fragment(RedirectInput.ri_split(rest, '#')), RedirectInput.ri_fragment(RedirectInput.ri_split(rest, '#')), rib.fragment(RedirectInput.ri_split(rest, '#'))) : {Ri.from_params([_]) == RedirectInput.ri_from_params([RedirectInput.ri_fragment(RedirectInput.ri_split(rest, '#'))]) : Ri.Answer}
      rib.from_params([RedirectInput.ri_fragment(RedirectInput.ri_split(rest, '#'))])
    case None{}:
      %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(v, '#'), RedirectInput.ri_split(v, '#'), rib.split(v, '#')) : {Ri.parse.hash(_, v) == RedirectInput.ri_parse.hash(RedirectInput.ri_split(v, '#'), v) : Ri.Answer}
      rib.parse.hash(RedirectInput.ri_split(v, '#'), v)

def rib.parse.query(+m: Maybe<&2, Ri.Cut>, +rest: String) -> {Ri.parse.query(m, rest) == RedirectInput.ri_parse.query(m, rest) : Ri.Answer}:
  match m:
    case None{}:
      %Equal.sym(String, Ri.unslash(rest), RedirectInput.ri_unslash(rest), rib.unslash(rest)) : {Ri.from_params([_, SNil{}]) == RedirectInput.ri_from_params([RedirectInput.ri_unslash(rest), SNil{}]) : Ri.Answer}
      rib.from_params([RedirectInput.ri_unslash(rest), SNil{}])
    case Some{+x}:
      match x:
        case Ri.Cut{+q, +f}:
          %Equal.sym(String, Ri.unslash(q), RedirectInput.ri_unslash(q), rib.unslash(q)) : {Ri.from_params([_, f]) == RedirectInput.ri_from_params([RedirectInput.ri_unslash(q), f]) : Ri.Answer}
          rib.from_params([RedirectInput.ri_unslash(q), f])

def rib.parse.at(+m: Maybe<&2, Ri.Cut>, +v: String) -> {Ri.parse.at(m, v) == RedirectInput.ri_parse.at(m, v) : Ri.Answer}:
  match m:
    case Some{+x}:
      match x:
        case Ri.Cut{+h, +rest}:
          %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(rest, '#'), RedirectInput.ri_split(rest, '#'), rib.split(rest, '#')) : {Ri.parse.query(_, rest) == RedirectInput.ri_parse.query(RedirectInput.ri_split(rest, '#'), rest) : Ri.Answer}
          rib.parse.query(RedirectInput.ri_split(rest, '#'), rest)
    case None{}:
      %Equal.sym(Maybe<&2, String>, Ri.scheme(v), RedirectInput.ri_scheme(v), rib.scheme(v)) : {Ri.parse.scheme(_, v) == RedirectInput.ri_parse.scheme(RedirectInput.ri_scheme(v), v) : Ri.Answer}
      rib.parse.scheme(RedirectInput.ri_scheme(v), v)

def rib.parse(+s: String) -> {Ri.parse(s) == RedirectInput.ri_parse(s) : Ri.Answer}:
  %Equal.sym(String, Ri.clean(s), RedirectInput.ri_clean(s), rib.clean(s)) : {Ri.parse.at(Ri.split(_, '?'), Ri.clean(s)) == RedirectInput.ri_parse.at(RedirectInput.ri_split(RedirectInput.ri_clean(s), '?'), RedirectInput.ri_clean(s)) : Ri.Answer}
  %Equal.sym(Maybe<&2, Ri.Cut>, Ri.split(RedirectInput.ri_clean(s), '?'), RedirectInput.ri_split(RedirectInput.ri_clean(s), '?'), rib.split(RedirectInput.ri_clean(s), '?')) : {Ri.parse.at(_, Ri.clean(s)) == RedirectInput.ri_parse.at(RedirectInput.ri_split(RedirectInput.ri_clean(s), '?'), RedirectInput.ri_clean(s)) : Ri.Answer}
  %Equal.sym(String, Ri.clean(s), RedirectInput.ri_clean(s), rib.clean(s)) : {Ri.parse.at(RedirectInput.ri_split(RedirectInput.ri_clean(s), '?'), _) == RedirectInput.ri_parse.at(RedirectInput.ri_split(RedirectInput.ri_clean(s), '?'), RedirectInput.ri_clean(s)) : Ri.Answer}
  rib.parse.at(RedirectInput.ri_split(RedirectInput.ri_clean(s), '?'), RedirectInput.ri_clean(s))

def rib.verify.at(+same: Bool, +code: String, +s: String) -> {Ri.verify.at(same, code, s) == RedirectInput.ri_verify.at(same, code, s) : Ri.Answer}:
  match same:
    case True{}:
      {==}
    case False{}:
      {==}

def rib.verify(+code: String, +m: Maybe<&2, String>, +expected: String) -> {Ri.verify(code, m, expected) == RedirectInput.ri_verify(code, m, expected) : Ri.Answer}:
  match m:
    case None{}:
      {==}
    case Some{+s}:
      rib.verify.at(String.eq(s, expected), code, s)

def rib.described(+m: Maybe<&2, String>) -> {Ri.described(m) == RedirectInput.ri_described(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{+d}:
      {==}

def rib.text(+f: Ri.Fail) -> {Ri.text(f) == RedirectInput.ri_text(f) : String}:
  match f:
    case Ri.FMissing{}:
      {==}
    case Ri.FMismatch{}:
      {==}
    case Ri.FProvider{+e, +d}:
      %Equal.sym(String, Ri.described(d), RedirectInput.ri_described(d), rib.described(d)) : {String.concat(["The sign-in page reported an error: ", e, _, ". Open the login link again and sign in, then paste the new address."]) == String.concat(["The sign-in page reported an error: ", e, RedirectInput.ri_described(d), ". Open the login link again and sign in, then paste the new address."]) : String}
      {==}

def rib.trim_start.at(+b: Bool, +c: Char, +t: String, +r: String) -> {Ri.trim_start.at(b, c, t, r) == RedirectInput.ri_trim_start.at(b, c, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rib.trim_start(+s: String) -> {Ri.trim_start(s) == RedirectInput.ri_trim_start(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Ri.trim_start(t), RedirectInput.ri_trim_start(t), rib.trim_start(t)) : {Ri.trim_start.at(Ga.space(c), c, t, _) == RedirectInput.ri_trim_start.at(Ga.space(c), c, t, RedirectInput.ri_trim_start(t)) : String}
      rib.trim_start.at(Ga.space(c), c, t, RedirectInput.ri_trim_start(t))

def rib.dots.at(+b: Bool, +c: Char, +t: String, +r: String) -> {Ri.dots.at(b, c, t, r) == RedirectInput.ri_dots.at(b, c, t, r) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def rib.dots(+s: String) -> {Ri.dots(s) == RedirectInput.ri_dots(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %Equal.sym(String, Ri.dots(t), RedirectInput.ri_dots(t), rib.dots(t)) : {Ri.dots.at(Char.is_eq(c, '.'), c, t, _) == RedirectInput.ri_dots.at(Char.is_eq(c, '.'), c, t, RedirectInput.ri_dots(t)) : String}
      rib.dots.at(Char.is_eq(c, '.'), c, t, RedirectInput.ri_dots(t))

def rib.reason(+s: String) -> {Ri.reason(s) == RedirectInput.ri_reason(s) : String}:
  %Equal.sym(String, Ri.trim_start(s), RedirectInput.ri_trim_start(s), rib.trim_start(s)) : {String.reverse(Ri.dots(Ri.trim_start(String.reverse(_)))) == String.reverse(RedirectInput.ri_dots(RedirectInput.ri_trim_start(String.reverse(RedirectInput.ri_trim_start(s))))) : String}
  %Equal.sym(String, Ri.trim_start(String.reverse(RedirectInput.ri_trim_start(s))), RedirectInput.ri_trim_start(String.reverse(RedirectInput.ri_trim_start(s))), rib.trim_start(String.reverse(RedirectInput.ri_trim_start(s)))) : {String.reverse(Ri.dots(_)) == String.reverse(RedirectInput.ri_dots(RedirectInput.ri_trim_start(String.reverse(RedirectInput.ri_trim_start(s))))) : String}
  %Equal.sym(String, Ri.dots(RedirectInput.ri_trim_start(String.reverse(RedirectInput.ri_trim_start(s)))), RedirectInput.ri_dots(RedirectInput.ri_trim_start(String.reverse(RedirectInput.ri_trim_start(s)))), rib.dots(RedirectInput.ri_trim_start(String.reverse(RedirectInput.ri_trim_start(s))))) : {String.reverse(_) == String.reverse(RedirectInput.ri_dots(RedirectInput.ri_trim_start(String.reverse(RedirectInput.ri_trim_start(s))))) : String}
  {==}

def rib.notice(+s: String) -> {Ri.notice(s) == RedirectInput.ri_notice(s) : String}:
  %Equal.sym(String, Ri.reason(s), RedirectInput.ri_reason(s), rib.reason(s)) : {String.concat(["Login did not complete: ", _, ". Paste the address again, or open the login link again and sign in."]) == String.concat(["Login did not complete: ", RedirectInput.ri_reason(s), ". Paste the address again, or open the login link again and sign in."]) : String}
  {==}
