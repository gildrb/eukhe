# eukhe: the proof of LAW semver_parse_exact
#
# PROOF of LAW semver_parse_exact: a char reads as a digit or a dot only
# when it is that char (pe.sym_char: each compare of Sym.of is real
# equality). Reading the fields keeps an invariant: the fields read and
# the field being read, written before the rest of the text, are the
# text (pe.text; Wf writes the fields as Num.str does, so each step is
# definitional). Three fields that read as numbers are the digits
# Num.dec writes for them (pe.read_inv), so the text is Ver.show(v).

import Base
import ../../bend/semver.bend as Sv
import ../../laws/semver.bend as Semver
import ../base/logic/logic.bend as LLogicLogic
import ../base/semver.bend as LSemver
import ../wire/wire_nat_exact.bend as PWireNatExact

# Chars
# -----

# Char.is_eq is real equality
def pe.char_sound(c: Char, k: Char, e: {Char.is_eq(c, k) == True{} : Bool}) -> {c == k : Char}:
  match c k:
    case Chr{+x} Chr{+y}:
      Equal.cong(U32, Char, z => Chr{z}, x, y, PWireNatExact.wn_eq_sound(x, y, e))

# what a symbol says about the char it was read from
def pe.SymChar(c: Char, y: Sv.Sym) -> Type:
  match y:
    case Sv.Digit{d}:
      {c == Sv.Dig.chr(d) : Char}
    case Sv.Dot{}:
      {c == '.' : Char}
    case Sv.Other{}:
      Unit

def pe.when(+c: Char, b: Bool, +k: Char, eb: {Char.is_eq(c, k) == b : Bool}, -y: Sv.Sym, -miss: Sv.Sym, py: {c == k : Char} -> pe.SymChar(c, y), pm: pe.SymChar(c, miss)) -> pe.SymChar(c, Sv.Sym.when(b, y, miss)):
  match b:
    case True{}:
      py(pe.char_sound(c, k, eb))
    case False{}:
      pm

# a char reads as a digit or a dot only when it is that char
def pe.sym_char(+c: Char) -> pe.SymChar(c, Sv.Sym.of(c)):
  pe.when(c, Char.is_eq(c, '0'), '0', {==}, Sv.Digit{Sv.D0{}}, Sv.Sym.when(Char.is_eq(c, '1'), Sv.Digit{Sv.D1{}}, Sv.Sym.when(Char.is_eq(c, '2'), Sv.Digit{Sv.D2{}}, Sv.Sym.when(Char.is_eq(c, '3'), Sv.Digit{Sv.D3{}}, Sv.Sym.when(Char.is_eq(c, '4'), Sv.Digit{Sv.D4{}}, Sv.Sym.when(Char.is_eq(c, '5'), Sv.Digit{Sv.D5{}}, Sv.Sym.when(Char.is_eq(c, '6'), Sv.Digit{Sv.D6{}}, Sv.Sym.when(Char.is_eq(c, '7'), Sv.Digit{Sv.D7{}}, Sv.Sym.when(Char.is_eq(c, '8'), Sv.Digit{Sv.D8{}}, Sv.Sym.when(Char.is_eq(c, '9'), Sv.Digit{Sv.D9{}}, Sv.Sym.when(Char.is_eq(c, '.'), Sv.Dot{}, Sv.Other{})))))))))), (e => e),
    pe.when(c, Char.is_eq(c, '1'), '1', {==}, Sv.Digit{Sv.D1{}}, Sv.Sym.when(Char.is_eq(c, '2'), Sv.Digit{Sv.D2{}}, Sv.Sym.when(Char.is_eq(c, '3'), Sv.Digit{Sv.D3{}}, Sv.Sym.when(Char.is_eq(c, '4'), Sv.Digit{Sv.D4{}}, Sv.Sym.when(Char.is_eq(c, '5'), Sv.Digit{Sv.D5{}}, Sv.Sym.when(Char.is_eq(c, '6'), Sv.Digit{Sv.D6{}}, Sv.Sym.when(Char.is_eq(c, '7'), Sv.Digit{Sv.D7{}}, Sv.Sym.when(Char.is_eq(c, '8'), Sv.Digit{Sv.D8{}}, Sv.Sym.when(Char.is_eq(c, '9'), Sv.Digit{Sv.D9{}}, Sv.Sym.when(Char.is_eq(c, '.'), Sv.Dot{}, Sv.Other{}))))))))), (e => e),
    pe.when(c, Char.is_eq(c, '2'), '2', {==}, Sv.Digit{Sv.D2{}}, Sv.Sym.when(Char.is_eq(c, '3'), Sv.Digit{Sv.D3{}}, Sv.Sym.when(Char.is_eq(c, '4'), Sv.Digit{Sv.D4{}}, Sv.Sym.when(Char.is_eq(c, '5'), Sv.Digit{Sv.D5{}}, Sv.Sym.when(Char.is_eq(c, '6'), Sv.Digit{Sv.D6{}}, Sv.Sym.when(Char.is_eq(c, '7'), Sv.Digit{Sv.D7{}}, Sv.Sym.when(Char.is_eq(c, '8'), Sv.Digit{Sv.D8{}}, Sv.Sym.when(Char.is_eq(c, '9'), Sv.Digit{Sv.D9{}}, Sv.Sym.when(Char.is_eq(c, '.'), Sv.Dot{}, Sv.Other{})))))))), (e => e),
    pe.when(c, Char.is_eq(c, '3'), '3', {==}, Sv.Digit{Sv.D3{}}, Sv.Sym.when(Char.is_eq(c, '4'), Sv.Digit{Sv.D4{}}, Sv.Sym.when(Char.is_eq(c, '5'), Sv.Digit{Sv.D5{}}, Sv.Sym.when(Char.is_eq(c, '6'), Sv.Digit{Sv.D6{}}, Sv.Sym.when(Char.is_eq(c, '7'), Sv.Digit{Sv.D7{}}, Sv.Sym.when(Char.is_eq(c, '8'), Sv.Digit{Sv.D8{}}, Sv.Sym.when(Char.is_eq(c, '9'), Sv.Digit{Sv.D9{}}, Sv.Sym.when(Char.is_eq(c, '.'), Sv.Dot{}, Sv.Other{}))))))), (e => e),
    pe.when(c, Char.is_eq(c, '4'), '4', {==}, Sv.Digit{Sv.D4{}}, Sv.Sym.when(Char.is_eq(c, '5'), Sv.Digit{Sv.D5{}}, Sv.Sym.when(Char.is_eq(c, '6'), Sv.Digit{Sv.D6{}}, Sv.Sym.when(Char.is_eq(c, '7'), Sv.Digit{Sv.D7{}}, Sv.Sym.when(Char.is_eq(c, '8'), Sv.Digit{Sv.D8{}}, Sv.Sym.when(Char.is_eq(c, '9'), Sv.Digit{Sv.D9{}}, Sv.Sym.when(Char.is_eq(c, '.'), Sv.Dot{}, Sv.Other{})))))), (e => e),
    pe.when(c, Char.is_eq(c, '5'), '5', {==}, Sv.Digit{Sv.D5{}}, Sv.Sym.when(Char.is_eq(c, '6'), Sv.Digit{Sv.D6{}}, Sv.Sym.when(Char.is_eq(c, '7'), Sv.Digit{Sv.D7{}}, Sv.Sym.when(Char.is_eq(c, '8'), Sv.Digit{Sv.D8{}}, Sv.Sym.when(Char.is_eq(c, '9'), Sv.Digit{Sv.D9{}}, Sv.Sym.when(Char.is_eq(c, '.'), Sv.Dot{}, Sv.Other{}))))), (e => e),
    pe.when(c, Char.is_eq(c, '6'), '6', {==}, Sv.Digit{Sv.D6{}}, Sv.Sym.when(Char.is_eq(c, '7'), Sv.Digit{Sv.D7{}}, Sv.Sym.when(Char.is_eq(c, '8'), Sv.Digit{Sv.D8{}}, Sv.Sym.when(Char.is_eq(c, '9'), Sv.Digit{Sv.D9{}}, Sv.Sym.when(Char.is_eq(c, '.'), Sv.Dot{}, Sv.Other{})))), (e => e),
    pe.when(c, Char.is_eq(c, '7'), '7', {==}, Sv.Digit{Sv.D7{}}, Sv.Sym.when(Char.is_eq(c, '8'), Sv.Digit{Sv.D8{}}, Sv.Sym.when(Char.is_eq(c, '9'), Sv.Digit{Sv.D9{}}, Sv.Sym.when(Char.is_eq(c, '.'), Sv.Dot{}, Sv.Other{}))), (e => e),
    pe.when(c, Char.is_eq(c, '8'), '8', {==}, Sv.Digit{Sv.D8{}}, Sv.Sym.when(Char.is_eq(c, '9'), Sv.Digit{Sv.D9{}}, Sv.Sym.when(Char.is_eq(c, '.'), Sv.Dot{}, Sv.Other{})), (e => e),
    pe.when(c, Char.is_eq(c, '9'), '9', {==}, Sv.Digit{Sv.D9{}}, Sv.Sym.when(Char.is_eq(c, '.'), Sv.Dot{}, Sv.Other{}), (e => e),
    pe.when(c, Char.is_eq(c, '.'), '.', {==}, Sv.Dot{}, Sv.Other{}, (e => e),
    Unit{})))))))))))

# Fields
# ------

# the fields fs (last first) written before x, as Num.str writes them
def pe.Wf(fs: List<&2, List<&2, Sv.Dig>>, x: String) -> String:
  match fs:
    case Nil{}:
      x
    case f <> rest:
      pe.Wf(rest, Sv.Num.str(f, SCon{'.', x}))

# the text of the fields read (last first)
def pe.Wo(m: Maybe<&2, List<&2, List<&2, Sv.Dig>>>) -> String:
  match m:
    case None{}:
      ""
    case Some{out}:
      match out:
        case Nil{}:
          ""
        case f <> rest:
          pe.Wf(rest, Sv.Num.str(f, ""))

def pe.text_sym(-c: Char, -t: String, y: Sv.Sym, k: pe.SymChar(c, y), +cur: List<&2, Sv.Dig>, +fs: List<&2, List<&2, Sv.Dig>>, -out: List<&2, List<&2, Sv.Dig>>,
  h: {Sv.Ver.fields(y <> Sv.Sym.list(t), cur, fs) == Some{out} : Maybe<&2, List<&2, List<&2, Sv.Dig>>>},
  ih: @c2: List<&2, Sv.Dig> -> @f2: List<&2, List<&2, Sv.Dig>> -> {Sv.Ver.fields(Sv.Sym.list(t), c2, f2) == Some{out} : Maybe<&2, List<&2, List<&2, Sv.Dig>>>} -> {pe.Wf(f2, Sv.Num.str(c2, t)) == pe.Wo(Some{out}) : String}) ->
  {pe.Wf(fs, Sv.Num.str(cur, SCon{c, t})) == pe.Wo(Some{out}) : String}:
  match y:
    case Sv.Digit{+d}:
      %Equal.sym(Char, c, Sv.Dig.chr(d), k) : {pe.Wf(fs, Sv.Num.str(cur, SCon{_, t})) == pe.Wo(Some{out}) : String}
      ih(d <> cur, fs, h)
    case Sv.Dot{}:
      %Equal.sym(Char, c, '.', k) : {pe.Wf(fs, Sv.Num.str(cur, SCon{_, t})) == pe.Wo(Some{out}) : String}
      ih(Nil{}, cur <> fs, h)
    case Sv.Other{}:
      LLogicLogic.themes.pt.none_some({pe.Wf(fs, Sv.Num.str(cur, SCon{c, t})) == pe.Wo(Some{out}) : String}, List<&2, List<&2, Sv.Dig>>, out, h)

# the fields read and the field being read, written before the rest of
# the text, are the text the fields read write
def pe.text(s: String, +cur: List<&2, Sv.Dig>, +fs: List<&2, List<&2, Sv.Dig>>, +out: List<&2, List<&2, Sv.Dig>>,
  h: {Sv.Ver.fields(Sv.Sym.list(s), cur, fs) == Some{out} : Maybe<&2, List<&2, List<&2, Sv.Dig>>>}) ->
  {pe.Wf(fs, Sv.Num.str(cur, s)) == pe.Wo(Some{out}) : String}:
  match s:
    case SNil{}:
      Equal.cong(Maybe<&2, List<&2, List<&2, Sv.Dig>>>, String, m => pe.Wo(m), Some{cur <> fs}, Some{out}, h)
    case SCon{+c, +t}:
      pe.text_sym(c, t, Sv.Sym.of(c), pe.sym_char(c), cur, fs, out, h,
        c2 => f2 => h2 => pe.text(t, c2, f2, out, h2))

# Numbers
# -------

def pe.some_inj(-A: Data, +a: A, -b: A, e: {Some{a} == Some{b} : Maybe<&2, A>}) -> {a == b : A}:
  Equal.cong(Maybe<&2, A>, A, m => Maybe.default(&2, A, m, a), Some{a}, Some{b}, e)

def pe.read_ok(+ds: List<&2, Sv.Dig>, ok: Bool, -x: Nat, eo: {Sv.Num.digs_eq(Sv.Num.dec(Sv.Num.val(ds)), ds) == ok : Bool}, h: {Sv.Num.read.ok(Sv.Num.val(ds), ok) == Some{x} : Maybe<&2, Nat>}) -> {ds == Sv.Num.dec(x) : List<&2, Sv.Dig>}:
  match ok:
    case True{}:
      +ex = pe.some_inj(Nat, Sv.Num.val(ds), x, h)
      %ex : {ds == Sv.Num.dec(_) : List<&2, Sv.Dig>}
      Equal.sym(List<&2, Sv.Dig>, Sv.Num.dec(Sv.Num.val(ds)), ds, LSemver.rk.digs_sound(Sv.Num.dec(Sv.Num.val(ds)), ds, eo))
    case False{}:
      LLogicLogic.themes.pt.none_some({ds == Sv.Num.dec(x) : List<&2, Sv.Dig>}, Nat, x, h)

# a field that reads as x is the digits Num.dec writes for x
def pe.read_inv(+ds: List<&2, Sv.Dig>, -x: Nat, h: {Sv.Num.read(ds) == Some{x} : Maybe<&2, Nat>}) -> {ds == Sv.Num.dec(x) : List<&2, Sv.Dig>}:
  pe.read_ok(ds, Sv.Num.digs_eq(Sv.Num.dec(Sv.Num.val(ds)), ds), x, {==}, h)

# Versions
# --------

def pe.of3(+a3: List<&2, Sv.Dig>, +b3: List<&2, Sv.Dig>, +c3: List<&2, Sv.Dig>, ra: Maybe<&2, Nat>, rb: Maybe<&2, Nat>, rc: Maybe<&2, Nat>,
  ea: {Sv.Num.read(a3) == ra : Maybe<&2, Nat>}, eb: {Sv.Num.read(b3) == rb : Maybe<&2, Nat>}, ec: {Sv.Num.read(c3) == rc : Maybe<&2, Nat>},
  -v: Sv.Ver, h: {Sv.Ver.of3(ra, rb, rc) == Some{v} : Maybe<&2, Sv.Ver>}) ->
  {Sv.Num.str(a3, SCon{'.', Sv.Num.str(b3, SCon{'.', Sv.Num.str(c3, "")})}) == Sv.Ver.show(v) : String}:
  match ra rb rc:
    case Some{+x} Some{+y} Some{+z}:
      %pe.some_inj(Sv.Ver, Sv.Ver{x, y, z}, v, h) : {Sv.Num.str(a3, SCon{'.', Sv.Num.str(b3, SCon{'.', Sv.Num.str(c3, "")})}) == Sv.Ver.show(_) : String}
      %Equal.sym(List<&2, Sv.Dig>, a3, Sv.Num.dec(x), pe.read_inv(a3, x, ea)) : {Sv.Num.str(_, SCon{'.', Sv.Num.str(b3, SCon{'.', Sv.Num.str(c3, "")})}) == Sv.Ver.show(Sv.Ver{x, y, z}) : String}
      %Equal.sym(List<&2, Sv.Dig>, b3, Sv.Num.dec(y), pe.read_inv(b3, y, eb)) : {Sv.Num.str(Sv.Num.dec(x), SCon{'.', Sv.Num.str(_, SCon{'.', Sv.Num.str(c3, "")})}) == Sv.Ver.show(Sv.Ver{x, y, z}) : String}
      %Equal.sym(List<&2, Sv.Dig>, c3, Sv.Num.dec(z), pe.read_inv(c3, z, ec)) : {Sv.Num.str(Sv.Num.dec(x), SCon{'.', Sv.Num.str(Sv.Num.dec(y), SCon{'.', Sv.Num.str(_, "")})}) == Sv.Ver.show(Sv.Ver{x, y, z}) : String}
      {==}
    case Some{x} Some{y} None{}:
      LLogicLogic.themes.pt.none_some({Sv.Num.str(a3, SCon{'.', Sv.Num.str(b3, SCon{'.', Sv.Num.str(c3, "")})}) == Sv.Ver.show(v) : String}, Sv.Ver, v, h)
    case Some{x} None{} _:
      LLogicLogic.themes.pt.none_some({Sv.Num.str(a3, SCon{'.', Sv.Num.str(b3, SCon{'.', Sv.Num.str(c3, "")})}) == Sv.Ver.show(v) : String}, Sv.Ver, v, h)
    case None{} _ _:
      LLogicLogic.themes.pt.none_some({Sv.Num.str(a3, SCon{'.', Sv.Num.str(b3, SCon{'.', Sv.Num.str(c3, "")})}) == Sv.Ver.show(v) : String}, Sv.Ver, v, h)

def pe.fields(+s: String, m: Maybe<&2, List<&2, List<&2, Sv.Dig>>>, em: {Sv.Ver.fields(Sv.Sym.list(s), Nil{}, Nil{}) == m : Maybe<&2, List<&2, List<&2, Sv.Dig>>>}, -v: Sv.Ver, h: {Sv.Ver.of_fields(m) == Some{v} : Maybe<&2, Sv.Ver>}) -> {s == Sv.Ver.show(v) : String}:
  match m:
    case None{}:
      LLogicLogic.themes.pt.none_some({s == Sv.Ver.show(v) : String}, Sv.Ver, v, h)
    case Some{fl}:
      match fl:
        case Nil{}:
          LLogicLogic.themes.pt.none_some({s == Sv.Ver.show(v) : String}, Sv.Ver, v, h)
        case x <> Nil{}:
          LLogicLogic.themes.pt.none_some({s == Sv.Ver.show(v) : String}, Sv.Ver, v, h)
        case x <> y <> Nil{}:
          LLogicLogic.themes.pt.none_some({s == Sv.Ver.show(v) : String}, Sv.Ver, v, h)
        case +c3 <> +b3 <> +a3 <> Nil{}:
          Equal.trans(String, s, Sv.Num.str(a3, SCon{'.', Sv.Num.str(b3, SCon{'.', Sv.Num.str(c3, "")})}), Sv.Ver.show(v),
            pe.text(s, Nil{}, Nil{}, [c3, b3, a3], em),
            pe.of3(a3, b3, c3, Sv.Num.read(a3), Sv.Num.read(b3), Sv.Num.read(c3), {==}, {==}, {==}, v, h))
        case x <> y <> z <> w <> more:
          LLogicLogic.themes.pt.none_some({s == Sv.Ver.show(v) : String}, Sv.Ver, v, h)

def Semver.semver_parse_exact(s, v, h):
  pe.fields(s, Sv.Ver.fields(Sv.Sym.list(s), Nil{}, Nil{}), {==}, v, h)
