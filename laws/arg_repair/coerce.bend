# eukhe: the laws of area arg_repair, R7: values read as the declared type

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec

# (H1) Charitable argument repair: values (R7, spec/harness/arguments.bend S4)
# ---------------------------------------------------------------------------
# Ar.coerce, the reading every repaired argument's value gets
# (laws/arg_repair.bend arg_repair_outs). Every input is free: any declared
# name, `items.type`, value, text, f64 reading and shape. The rows below
# are S4's; whitespace, words and bounds come from outside the code: Unicode
# White_Space (PropList.txt), the requirement's boolean words (`true`,
# `1`, `yes`, `on`; `false`, `0`, `no`, `off`), Rust's i64 bounds
# (`i64::MIN` = -9223372036854775808, `i64::MAX` = 9223372036854775807) and
# `str::parse::<i64>`'s grammar `[+-]?[0-9]+`, RFC 8259's `true`/`false`.

# Spec helpers
# ------------

# a code point, or a range of them
type Cp is Data:
  CpOne{x: U32}
  CpSpan{lo: U32, hi: U32}

# Unicode White_Space (PropList.txt; Rust `char::is_whitespace`, which
# `str::trim` strips), in code point order
def sp_white_cps() -> List<&2, Cp>:
  [CpSpan{9, 13}, CpOne{32}, CpOne{133}, CpOne{160}, CpOne{5760}, CpSpan{8192, 8202}, CpOne{8232}, CpOne{8233}, CpOne{8239}, CpOne{8287}, CpOne{12288}]

def sp_in_cp(+x: U32, c: Cp) -> Bool:
  match c:
    case CpOne{y}:
      U32.is_eq(x, y)
    case CpSpan{lo, hi}:
      Bool.and(U32.is_ge(x, lo), U32.is_le(x, hi))

def sp_in_cps(+x: U32, cs: List<&2, Cp>) -> Bool:
  match cs:
    case Nil{}:
      False{}
    case c <> t:
      Bool.or(sp_in_cp(x, c), sp_in_cps(x, t))

def sp_white(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      sp_in_cps(x, sp_white_cps())

# every char of s is White_Space (the empty text too)
def sp_all_white(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(sp_white(c), sp_all_white(t))

# the last char of the text c then t is White_Space
def sp_ends_white(t: String, c: Char) -> Bool:
  match t:
    case SNil{}:
      sp_white(c)
    case SCon{d, u}:
      sp_ends_white(u, d)

# a text with no White_Space at either end (the empty text too): what
# `str::trim` leaves
def sp_bare(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, +u}:
      Bool.and(Bool.not(sp_white(c)), Bool.not(sp_ends_white(u, c)))

def sp_bare_m(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{u}:
      sp_bare(u)

def sp_lower.at(up: Bool, x: U32) -> U32:
  match up:
    case True{}:
      U32.add(x, 32)
    case False{}:
      x

# Rust `to_ascii_lowercase`: `A`..`Z` as `a`..`z`, every other char kept
def sp_lower(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          SCon{Chr{sp_lower.at(Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90)), x)}, sp_lower(t)}

def sp_bool.of(yes: Bool, no: Bool) -> Maybe<&2, Ar.To>:
  match yes:
    case True{}:
      Some{Ar.TBool{True{}}}
    case False{}:
      match no:
        case True{}:
          Some{Ar.TBool{False{}}}
        case False{}:
          None{}

# the requirement's boolean words, in its order
def sp_bool.word(+w: String) -> Maybe<&2, Ar.To>:
  sp_bool.of(ArgSpec.member(w, ["true", "1", "yes", "on"]), ArgSpec.member(w, ["false", "0", "no", "off"]))

# S4: the boolean a text (none past 4,096 chars) spells, its ASCII lower case
# one of the requirement's words
def sp_bool(m: Maybe<&2, String>) -> Maybe<&2, Ar.To>:
  match m:
    case None{}:
      None{}
    case Some{u}:
      sp_bool.word(sp_lower(u))

# a decimal digit
type Dig is Data:
  D0{}
  D1{}
  D2{}
  D3{}
  D4{}
  D5{}
  D6{}
  D7{}
  D8{}
  D9{}

def sp_dig(d: Dig) -> Char:
  match d:
    case D0{}:
      '0'
    case D1{}:
      '1'
    case D2{}:
      '2'
    case D3{}:
      '3'
    case D4{}:
      '4'
    case D5{}:
      '5'
    case D6{}:
      '6'
    case D7{}:
      '7'
    case D8{}:
      '8'
    case D9{}:
      '9'

def sp_zero(d: Dig) -> Bool:
  match d:
    case D0{}:
      True{}
    case D1{}:
      False{}
    case D2{}:
      False{}
    case D3{}:
      False{}
    case D4{}:
      False{}
    case D5{}:
      False{}
    case D6{}:
      False{}
    case D7{}:
      False{}
    case D8{}:
      False{}
    case D9{}:
      False{}

# the text of digits
def sp_digs(ds: List<&2, Dig>) -> String:
  match ds:
    case Nil{}:
      SNil{}
    case d <> t:
      SCon{sp_dig(d), sp_digs(t)}

# n zeros
def sp_zeros(n: Nat) -> String:
  match n:
    case 0n:
      SNil{}
    case 1n+p:
      SCon{'0', sp_zeros(p)}

# an integer's sign as written
type Sign is Data:
  SgNone{}
  SgPlus{}
  SgMinus{}

def sp_sign(s: Sign) -> String:
  match s:
    case SgNone{}:
      ""
    case SgPlus{}:
      "+"
    case SgMinus{}:
      "-"

# canonical digits d (no leading zero) fit i64 for a sign: fewer than 19
# digits, or 19 digits not past i64::MAX's (|i64::MIN|'s for `-`); digit
# strings of one length compare as numbers in digit order (String.is_le)
def sp_fits(s: Sign, +d: String) -> Bool:
  match s:
    case SgMinus{}:
      Bool.or(Nat.is_lt(String.length(d), 19n), Bool.and(Nat.is_eq(String.length(d), 19n), String.is_le(d, "9223372036854775808")))
    case SgNone{}:
      Bool.or(Nat.is_lt(String.length(d), 19n), Bool.and(Nat.is_eq(String.length(d), 19n), String.is_le(d, "9223372036854775807")))
    case SgPlus{}:
      Bool.or(Nat.is_lt(String.length(d), 19n), Bool.and(Nat.is_eq(String.length(d), 19n), String.is_le(d, "9223372036854775807")))

def sp_when(b: Bool, t: Ar.To) -> Maybe<&2, Ar.To>:
  match b:
    case True{}:
      Some{t}
    case False{}:
      None{}

# S4: the integer of sign s and canonical digits d (not zero), as its JSON
# text, when it fits i64
def sp_int(+s: Sign, +d: String) -> Maybe<&2, Ar.To>:
  match s:
    case SgMinus{}:
      sp_when(sp_fits(SgMinus{}, d), Ar.TNum{String.append("-", d)})
    case SgNone{}:
      sp_when(sp_fits(SgNone{}, d), Ar.TNum{d})
    case SgPlus{}:
      sp_when(sp_fits(SgPlus{}, d), Ar.TNum{d})

def sp_digit(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57))

def sp_all_digits(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(sp_digit(c), sp_all_digits(t))

# one or more ASCII digits
def sp_some_digits(+s: String) -> Bool:
  Bool.and(Bool.not(String.is_empty(s)), sp_all_digits(s))

def sp_int_text.at(minus: Bool, plus: Bool, c: Char, t: String) -> Bool:
  match minus:
    case True{}:
      sp_some_digits(t)
    case False{}:
      match plus:
        case True{}:
          sp_some_digits(t)
        case False{}:
          sp_some_digits(SCon{c, t})

# `[+-]?[0-9]+`: an optional sign, then one or more ASCII digits
def sp_int_text(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, t}:
      sp_int_text.at(Char.is_eq(c, '-'), Char.is_eq(c, '+'), c, t)

def sp_int_m(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{u}:
      sp_int_text(u)

# RFC 8259's literal names
def sp_json_bool(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"

# S4 for `string`: a number or a boolean as its JSON text; nothing else
def sp_as_string(v: Ar.Val) -> Maybe<&2, Ar.To>:
  match v:
    case Ar.VBool{b}:
      Some{Ar.TStr{sp_json_bool(b)}}
    case Ar.VNum{x}:
      Some{Ar.TStr{x}}
    case Ar.VNull{}:
      None{}
    case Ar.VStr{t, n, sh}:
      None{}
    case Ar.VArr{}:
      None{}
    case Ar.VObj{}:
      None{}

# S4 for `number`: a string's f64 reading; nothing else
def sp_as_number(v: Ar.Val) -> Maybe<&2, Ar.To>:
  match v:
    case Ar.VStr{t, n, sh}:
      match n:
        case Some{x}:
          Some{Ar.TNum{x}}
        case None{}:
          None{}
    case Ar.VNull{}:
      None{}
    case Ar.VBool{b}:
      None{}
    case Ar.VNum{x}:
      None{}
    case Ar.VArr{}:
      None{}
    case Ar.VObj{}:
      None{}

def sp_shape_obj(sh: Ar.Shape) -> Bool:
  match sh:
    case Ar.SBrace{o}:
      o
    case Ar.SPlain{}:
      False{}
    case Ar.SBracket{a}:
      False{}

# S4 for `object`: a string opening with `{` that reads as an object
def sp_as_object(v: Ar.Val) -> Maybe<&2, Ar.To>:
  match v:
    case Ar.VStr{t, n, sh}:
      sp_when(sp_shape_obj(sh), Ar.TObj{})
    case Ar.VNull{}:
      None{}
    case Ar.VBool{b}:
      None{}
    case Ar.VNum{x}:
      None{}
    case Ar.VArr{}:
      None{}
    case Ar.VObj{}:
      None{}

def sp_lone(it: Maybe<&2, String>) -> Maybe<&2, Ar.To>:
  match it:
    case Some{t}:
      sp_when(String.eq(t, "string"), Ar.TOne{})
    case None{}:
      None{}

def sp_as_array.str(it: Maybe<&2, String>, sh: Ar.Shape) -> Maybe<&2, Ar.To>:
  match sh:
    case Ar.SBracket{a}:
      sp_when(a, Ar.TArr{})
    case Ar.SPlain{}:
      sp_lone(it)
    case Ar.SBrace{o}:
      sp_lone(it)

# S4 for `array`: a string opening with `[` as the array it reads as (none
# when it reads as none); another string, for `items.type` `string`, as
# the one-item array of it
def sp_as_array(it: Maybe<&2, String>, v: Ar.Val) -> Maybe<&2, Ar.To>:
  match v:
    case Ar.VStr{t, n, sh}:
      sp_as_array.str(it, sh)
    case Ar.VNull{}:
      None{}
    case Ar.VBool{b}:
      None{}
    case Ar.VNum{x}:
      None{}
    case Ar.VArr{}:
      None{}
    case Ar.VObj{}:
      None{}

# Laws (R7)
# ---------

# LAW arg_repair_coerce_trims (R7, S4): a string's text with White_Space
# before and after it is read, for every declared argument, as the text
# alone (no White_Space at either end)
# EXCLUDES: ASCII-only trimming, U+0085 or U+3000 kept, U+FEFF trimmed, one
#   end trimmed, a char inside dropped
law arg_repair_coerce_trims:
  for +p: Maybe<&2, Ar.Prop>
  for +a: String
  for +u: String
  for +b: String
  for +n: Maybe<&2, String>
  for +sh: Ar.Shape
  for ha: {sp_all_white(a) == True{} : Bool}
  for hb: {sp_all_white(b) == True{} : Bool}
  for hu: {sp_bare(u) == True{} : Bool}
  {Ar.coerce(p, Ar.VStr{Some{String.append(a, String.append(u, b))}, n, sh}) == Ar.coerce(p, Ar.VStr{Some{u}, n, sh}) : Maybe<&2, Ar.To>}

# LAW arg_repair_coerce_bool (R7, S4): for `boolean`, a string whose text
# (trimmed) in ASCII lower case is one of the requirement's words is that
# boolean; any other text, or none (past 4,096 chars), is not read
# EXCLUDES: a word dropped or added, `on`/`off` swapped, a case-sensitive
#   reading, a non-ASCII char folded
law arg_repair_coerce_bool:
  for +n: String
  for +it: Maybe<&2, String>
  for +m: Maybe<&2, String>
  for +num: Maybe<&2, String>
  for +sh: Ar.Shape
  for hm: {sp_bare_m(m) == True{} : Bool}
  {Ar.coerce(Some{Ar.Prop{n, Some{"boolean"}, it}}, Ar.VStr{m, num, sh}) == sp_bool(m) : Maybe<&2, Ar.To>}

# LAW arg_repair_coerce_int (R7, S4): for `integer`, a sign, any zeros,
# then digits that open with no zero are the integer of those digits (`-`
# only for `-`) when it fits i64, else not read
# EXCLUDES: a bound off by one, |i64::MIN| refused, a leading zero kept, a
#   `+` kept, a length counted wrong
law arg_repair_coerce_int:
  for +n: String
  for +it: Maybe<&2, String>
  for +num: Maybe<&2, String>
  for +sh: Ar.Shape
  for +s: Sign
  for +z: Nat
  for +d: Dig
  for +ds: List<&2, Dig>
  for nz: {sp_zero(d) == False{} : Bool}
  {Ar.coerce(Some{Ar.Prop{n, Some{"integer"}, it}}, Ar.VStr{Some{String.append(sp_sign(s), String.append(sp_zeros(z), sp_digs(d <> ds)))}, num, sh}) == sp_int(s, sp_digs(d <> ds)) : Maybe<&2, Ar.To>}

# LAW arg_repair_coerce_int_zero (R7, S4): for `integer`, a sign then one
# or more zeros is 0 (`-0` too)
# EXCLUDES: `-0` read as `-0`, zeros refused
law arg_repair_coerce_int_zero:
  for +n: String
  for +it: Maybe<&2, String>
  for +num: Maybe<&2, String>
  for +sh: Ar.Shape
  for +s: Sign
  for +z: Nat
  {Ar.coerce(Some{Ar.Prop{n, Some{"integer"}, it}}, Ar.VStr{Some{String.append(sp_sign(s), sp_zeros(1n+z))}, num, sh}) == Some{Ar.TNum{"0"}} : Maybe<&2, Ar.To>}

# LAW arg_repair_coerce_int_text (R7, S4): for `integer`, a string with no
# text, or whose text (trimmed) is not `[+-]?[0-9]+`, is not read
# EXCLUDES: a sign alone, a sign doubled, a decimal point, a non-ASCII
#   digit read
law arg_repair_coerce_int_text:
  for +n: String
  for +it: Maybe<&2, String>
  for +m: Maybe<&2, String>
  for +num: Maybe<&2, String>
  for +sh: Ar.Shape
  for hm: {sp_bare_m(m) == True{} : Bool}
  for hi: {sp_int_m(m) == False{} : Bool}
  {Ar.coerce(Some{Ar.Prop{n, Some{"integer"}, it}}, Ar.VStr{m, num, sh}) == None{} : Maybe<&2, Ar.To>}

# LAW arg_repair_coerce_string (R7, S4): for `string`, a number or a
# boolean is its JSON text; nothing else is read
# EXCLUDES: `True`/`1` for a boolean, a string or a container read
law arg_repair_coerce_string:
  for +n: String
  for +it: Maybe<&2, String>
  for +v: Ar.Val
  {Ar.coerce(Some{Ar.Prop{n, Some{"string"}, it}}, v) == sp_as_string(v) : Maybe<&2, Ar.To>}

# LAW arg_repair_coerce_number (R7, S4): for `number`, a string is its f64
# reading (none: not read); nothing else is read
# EXCLUDES: a boolean read as a number, a string's text read instead
law arg_repair_coerce_number:
  for +n: String
  for +it: Maybe<&2, String>
  for +v: Ar.Val
  {Ar.coerce(Some{Ar.Prop{n, Some{"number"}, it}}, v) == sp_as_number(v) : Maybe<&2, Ar.To>}

# LAW arg_repair_coerce_object (R7, S4): for `object`, a string opening
# with `{` that reads as an object is that object; nothing else is read
# EXCLUDES: broken `{` text read, `[` text read as an object
law arg_repair_coerce_object:
  for +n: String
  for +it: Maybe<&2, String>
  for +v: Ar.Val
  {Ar.coerce(Some{Ar.Prop{n, Some{"object"}, it}}, v) == sp_as_object(v) : Maybe<&2, Ar.To>}

# LAW arg_repair_coerce_array (R7, S4): for `array`, a string opening with
# `[` is the array it reads as (broken: not read); another string is the
# one-item array of it when `items.type` is `string`; nothing else is read
# EXCLUDES: broken `[` text wrapped, a lone string wrapped for other items
law arg_repair_coerce_array:
  for +n: String
  for +it: Maybe<&2, String>
  for +v: Ar.Val
  {Ar.coerce(Some{Ar.Prop{n, Some{"array"}, it}}, v) == sp_as_array(it, v) : Maybe<&2, Ar.To>}
