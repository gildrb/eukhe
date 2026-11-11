# harness (spec): charitable argument repair (omp ADR 0020), restated
# without the repair code (bend/arg_repair.bend). The laws of area
# arg_repair (laws/arg_repair.bend) state that the code refines it. A
# spec: the shipped code never calls it.
#
# S1: a sent key in a JSON string (Rust: its decoding, up to 3 layers) is
#     read as its decoding, unless that is the key itself or another sent
#     key.
# S2: the key read so is refused when the dialect refuses it (the first
#     hint); else read as the canonical name of its first alias when it is
#     an undeclared alias, that name admitted as it would be sent: refused
#     when the dialect refuses it, unknown when a closed schema does not
#     declare it or when it is itself an undeclared alias (a chain); else
#     as itself when it is declared or the schema is open; else it is
#     unknown (the declared names, in order). A refusal names the key
#     refused: the canonical name for an alias's.
# S3: the arguments are read in order; the first that is refused, unknown,
#     or read as a name an earlier argument took (the key that took it
#     first) refuses the whole call.
# S4: a value of a declared argument with a `type` is read as that type
#     when it spells it: a number or boolean for `string` is its JSON text
#     (`true`/`false`); a string, trimmed of White_Space, for `boolean`
#     whose ASCII lower case is `true`, `yes`, `on`, `1` (true) or `false`,
#     `no`, `off`, `0` (false); for `integer` an optional `+`/`-` then
#     ASCII digits within -2^63..2^63-1, as its JSON text without leading
#     zeros; for `number` its f64 reading; for `object` (opening with `{`)
#     the object it reads as; for `array` (opening with `[`) the array it
#     reads as, else (`items.type` `string`) the one-item array of it. A
#     string past 4,096 chars has no text: no boolean, no integer.
# S5: each argument records, in order: its key decoded (S1), its key read
#     as another name (S2), its value read (S4); nothing else.

import Base
import ../../bend/arg_repair.bend as Ar

# S1-S2: keys
# -----------

# s is one of xs
def member(+s: String, xs: List<&2, String>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(String.eq(s, x), member(s, t))

def sent_keys(args: List<&2, Ar.Arg>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case a <> t:
      match a:
        case Ar.Arg{k, p, v}:
          k <> sent_keys(t)

def decoding.keep(drop: Bool, p: String) -> Maybe<&2, String>:
  match drop:
    case True{}:
      None{}
    case False{}:
      Some{p}

# S1: the decoding a sent key is read as, if any
def decoding(+ks: List<&2, String>, +k: String, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{+p}:
      decoding.keep(Bool.or(String.eq(p, k), member(p, ks)), p)

def first_text.at(hit: Bool, x: String, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      r

# the text of the first pair keyed k
def first_text(+k: String, kvs: List<&2, Ar.KV>) -> Maybe<&2, String>:
  match kvs:
    case Nil{}:
      None{}
    case e <> t:
      match e:
        case Ar.KV{+x, c}:
          first_text.at(String.eq(k, x), c, first_text(k, t))

def declared_names(ps: List<&2, Ar.Prop>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      match p:
        case Ar.Prop{n, k, i}:
          n <> declared_names(t)

def declared.at(hit: Bool, p: Ar.Prop, r: Maybe<&2, Ar.Prop>) -> Maybe<&2, Ar.Prop>:
  match hit:
    case True{}:
      Some{p}
    case False{}:
      r

# the first declared argument named k
def declared(+k: String, ps: List<&2, Ar.Prop>) -> Maybe<&2, Ar.Prop>:
  match ps:
    case Nil{}:
      None{}
    case p <> t:
      match p:
        case Ar.Prop{+n, i, j}:
          declared.at(String.eq(k, n), Ar.Prop{n, i, j}, declared(k, t))

def is_some(m: Maybe<&2, Ar.Prop>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{p}:
      True{}

def name.own(dec: Bool, closed: Bool, +k: String, ps: List<&2, Ar.Prop>) -> Ar.Named:
  match dec:
    case True{}:
      Ar.NAs{k}
    case False{}:
      match closed:
        case True{}:
          Ar.NUnknown{k, declared_names(ps)}
        case False{}:
          Ar.NAs{k}

def name.chain(al: Maybe<&2, String>, +c: String, ps: List<&2, Ar.Prop>) -> Ar.Named:
  match al:
    case None{}:
      Ar.NAs{c}
    case Some{e}:
      Ar.NUnknown{c, declared_names(ps)}

# S2: an alias's canonical name c, admitted as the key c sent would be
def name.target(h: Maybe<&2, String>, dec: Bool, closed: Bool, al: Maybe<&2, String>, +c: String, ps: List<&2, Ar.Prop>) -> Ar.Named:
  match h:
    case Some{x}:
      Ar.NRefused{c, x}
    case None{}:
      match dec:
        case True{}:
          Ar.NAs{c}
        case False{}:
          match closed:
            case True{}:
              Ar.NUnknown{c, declared_names(ps)}
            case False{}:
              name.chain(al, c, ps)

def name.alias(al: Maybe<&2, String>, dec: Bool, closed: Bool, +k: String, +ps: List<&2, Ar.Prop>, als: List<&2, Ar.KV>, rs: List<&2, Ar.KV>) -> Ar.Named:
  match al:
    case Some{+c}:
      match dec:
        case True{}:
          Ar.NAs{k}
        case False{}:
          name.target(first_text(c, rs), is_some(declared(c, ps)), closed, first_text(c, als), c, ps)
    case None{}:
      name.own(dec, closed, k, ps)

def name.refused(h: Maybe<&2, String>, sc: Ar.Schema, +als: List<&2, Ar.KV>, rs: List<&2, Ar.KV>, +k: String) -> Ar.Named:
  match h:
    case Some{x}:
      Ar.NRefused{k, x}
    case None{}:
      match sc:
        case Ar.Schema{+ps, cl}:
          name.alias(first_text(k, als), is_some(declared(k, ps)), cl, k, ps, als, rs)

# S2: what the key read is
def name(sc: Ar.Schema, d: Ar.Dialect, +k: String) -> Ar.Named:
  match d:
    case Ar.Dialect{als, +rs}:
      name.refused(first_text(k, rs), sc, als, rs, k)

# S4: values
# ----------

def kind.of(t: String, s: Bool, b: Bool, i: Bool, n: Bool, o: Bool, a: Bool) -> Ar.Ty:
  match s:
    case True{}:
      Ar.KString{}
    case False{}:
      match b:
        case True{}:
          Ar.KBoolean{}
        case False{}:
          match i:
            case True{}:
              Ar.KInteger{}
            case False{}:
              match n:
                case True{}:
                  Ar.KNumber{}
                case False{}:
                  match o:
                    case True{}:
                      Ar.KObject{}
                    case False{}:
                      match a:
                        case True{}:
                          Ar.KArray{}
                        case False{}:
                          Ar.KOther{}

# the declared type named t
def kind(+t: String) -> Ar.Ty:
  kind.of(t, String.eq(t, "string"), String.eq(t, "boolean"), String.eq(t, "integer"), String.eq(t, "number"), String.eq(t, "object"), String.eq(t, "array"))

# Unicode White_Space (Rust `char::is_whitespace`)
def white.code(+x: U32) -> Bool:
  Bool.or(Bool.and(U32.is_ge(x, 9), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 133), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_ge(x, 8192), U32.is_le(x, 8202)), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), U32.is_eq(x, 12288)))))))))))

def white(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      white.code(x)

def lead.at(w: Bool, c: Char, t: String, r: String) -> String:
  match w:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without leading White_Space
def lead(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      lead.at(white(c), c, t, lead(t))

# s without leading and trailing White_Space (Rust `str::trim`)
def trimmed(s: String) -> String:
  String.reverse(lead(String.reverse(lead(s))))

def small.at(up: Bool, x: U32) -> U32:
  match up:
    case True{}:
      U32.add(x, 32)
    case False{}:
      x

# s with A-Z as a-z (Rust `to_ascii_lowercase`)
def small(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          SCon{Chr{small.at(Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90)), x)}, small(t)}

def truth.of(yes: Bool, no: Bool) -> Maybe<&2, Ar.To>:
  match yes:
    case True{}:
      Some{Ar.TBool{True{}}}
    case False{}:
      match no:
        case True{}:
          Some{Ar.TBool{False{}}}
        case False{}:
          None{}

# the boolean a lower-case word spells
def truth(+w: String) -> Maybe<&2, Ar.To>:
  truth.of(member(w, ["true", "yes", "on", "1"]), member(w, ["false", "no", "off", "0"]))

def digit(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57))

def all_digits(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(digit(c), all_digits(t))

def nozero.at(z: Bool, c: Char, t: String, r: String) -> String:
  match z:
    case True{}:
      r
    case False{}:
      SCon{c, t}

def nozero(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      nozero.at(Char.is_eq(c, '0'), c, t, nozero(t))

def plain_digits.fin(s: String) -> String:
  match s:
    case SNil{}:
      "0"
    case SCon{c, t}:
      SCon{c, t}

# digits without leading zeros; `0` for none
def plain_digits(s: String) -> String:
  plain_digits.fin(nozero(s))

# canonical digits a no larger than b
def not_above(+a: String, +b: String) -> Bool:
  +la = String.length(a)
  +lb = String.length(b)
  Bool.or(Nat.is_lt(la, lb), Bool.and(Nat.is_eq(la, lb), String.is_le(a, b)))

def integer.in(ok: Bool, text: String) -> Maybe<&2, Ar.To>:
  match ok:
    case True{}:
      Some{Ar.TNum{text}}
    case False{}:
      None{}

def integer.minus.at(zero: Bool, +c: String) -> Maybe<&2, Ar.To>:
  match zero:
    case True{}:
      integer.in(True{}, "0")
    case False{}:
      integer.in(not_above(c, "9223372036854775808"), SCon{'-', c})

def integer.minus(+c: String) -> Maybe<&2, Ar.To>:
  integer.minus.at(String.eq(c, "0"), c)

def integer.signed(neg: Bool, +c: String) -> Maybe<&2, Ar.To>:
  match neg:
    case True{}:
      integer.minus(c)
    case False{}:
      integer.in(not_above(c, "9223372036854775807"), c)

def integer.body.at(ok: Bool, neg: Bool, d: String) -> Maybe<&2, Ar.To>:
  match ok:
    case True{}:
      integer.signed(neg, plain_digits(d))
    case False{}:
      None{}

def integer.body(neg: Bool, +d: String) -> Maybe<&2, Ar.To>:
  integer.body.at(Bool.and(Bool.not(String.is_empty(d)), all_digits(d)), neg, d)

def integer.lead(minus: Bool, plus: Bool, c: Char, t: String) -> Maybe<&2, Ar.To>:
  match minus:
    case True{}:
      integer.body(True{}, t)
    case False{}:
      match plus:
        case True{}:
          integer.body(False{}, t)
        case False{}:
          integer.body(False{}, SCon{c, t})

# the i64 a trimmed text spells
def integer(s: String) -> Maybe<&2, Ar.To>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, t}:
      integer.lead(Char.is_eq(c, '-'), Char.is_eq(c, '+'), c, t)

def read_bool(m: Maybe<&2, String>) -> Maybe<&2, Ar.To>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      truth(small(trimmed(s)))

def read_int(m: Maybe<&2, String>) -> Maybe<&2, Ar.To>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      integer(trimmed(s))

def read_num(m: Maybe<&2, String>) -> Maybe<&2, Ar.To>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{Ar.TNum{x}}

def read_obj(sh: Ar.Shape) -> Maybe<&2, Ar.To>:
  match sh:
    case Ar.SPlain{}:
      None{}
    case Ar.SBrace{o}:
      match o:
        case True{}:
          Some{Ar.TObj{}}
        case False{}:
          None{}
    case Ar.SBracket{a}:
      None{}

def lone.at(b: Bool) -> Maybe<&2, Ar.To>:
  match b:
    case True{}:
      Some{Ar.TOne{}}
    case False{}:
      None{}

def lone(it: Maybe<&2, String>) -> Maybe<&2, Ar.To>:
  match it:
    case None{}:
      None{}
    case Some{t}:
      lone.at(String.eq(t, "string"))

def read_arr(sh: Ar.Shape, it: Maybe<&2, String>) -> Maybe<&2, Ar.To>:
  match sh:
    case Ar.SPlain{}:
      lone(it)
    case Ar.SBrace{o}:
      lone(it)
    case Ar.SBracket{a}:
      match a:
        case True{}:
          Some{Ar.TArr{}}
        case False{}:
          None{}

def read_str(k: Ar.Ty, it: Maybe<&2, String>, text: Maybe<&2, String>, num: Maybe<&2, String>, sh: Ar.Shape) -> Maybe<&2, Ar.To>:
  match k:
    case Ar.KString{}:
      None{}
    case Ar.KBoolean{}:
      read_bool(text)
    case Ar.KInteger{}:
      read_int(text)
    case Ar.KNumber{}:
      read_num(num)
    case Ar.KObject{}:
      read_obj(sh)
    case Ar.KArray{}:
      read_arr(sh, it)
    case Ar.KOther{}:
      None{}

def text_of(k: Ar.Ty, text: String) -> Maybe<&2, Ar.To>:
  match k:
    case Ar.KString{}:
      Some{Ar.TStr{text}}
    case Ar.KBoolean{}:
      None{}
    case Ar.KInteger{}:
      None{}
    case Ar.KNumber{}:
      None{}
    case Ar.KObject{}:
      None{}
    case Ar.KArray{}:
      None{}
    case Ar.KOther{}:
      None{}

def bool_word(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"

def read_val(+k: Ar.Ty, it: Maybe<&2, String>, v: Ar.Val) -> Maybe<&2, Ar.To>:
  match v:
    case Ar.VNull{}:
      None{}
    case Ar.VBool{b}:
      text_of(k, bool_word(b))
    case Ar.VNum{x}:
      text_of(k, x)
    case Ar.VStr{t, n, sh}:
      read_str(k, it, t, n, sh)
    case Ar.VArr{}:
      None{}
    case Ar.VObj{}:
      None{}

# S4: v as the declared argument p reads it (none: kept)
def read(p: Maybe<&2, Ar.Prop>, v: Ar.Val) -> Maybe<&2, Ar.To>:
  match p:
    case None{}:
      None{}
    case Some{q}:
      match q:
        case Ar.Prop{n, k, it}:
          match k:
            case None{}:
              None{}
            case Some{t}:
              read_val(kind(t), it, v)

# S3, S5: the call
# ----------------

# the key sent first for the name c among the names taken
def taken.at(hit: Bool, x: String, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match hit:
    case True{}:
      Some{x}
    case False{}:
      r

def taken(+c: String, ss: List<&2, Ar.Seen>) -> Maybe<&2, String>:
  match ss:
    case Nil{}:
      None{}
    case s <> t:
      match s:
        case Ar.Seen{+n, k}:
          taken.at(String.eq(c, n), k, taken(c, t))

def renamed(same: Bool, k: String, c: String) -> List<&2, Ar.Record>:
  match same:
    case True{}:
      Nil{}
    case False{}:
      [Ar.RAlias{k, c}]

def read_rec(c: String, v: Ar.Val, to: Maybe<&2, Ar.To>) -> List<&2, Ar.Record>:
  match to:
    case None{}:
      Nil{}
    case Some{x}:
      [Ar.RCoerce{c, v, x}]

def take.ok(same: Bool, +c: String, +to: Maybe<&2, Ar.To>, pre: List<&2, Ar.Record>, +k: String, v: Ar.Val) -> Ar.Step:
  Ar.StepOk{Ar.Out{c, to}, List.append(&2, Ar.Record, pre, List.append(&2, Ar.Record, renamed(same, k, c), read_rec(c, v, to))), Ar.Seen{c, k}}

def take.free(f: Maybe<&2, String>, +c: String, ps: List<&2, Ar.Prop>, pre: List<&2, Ar.Record>, +k: String, +v: Ar.Val) -> Ar.Step:
  match f:
    case Some{x}:
      Ar.StepNo{Ar.Ambiguous{c, x, k}}
    case None{}:
      take.ok(String.eq(c, k), c, read(declared(c, ps), v), pre, k, v)

def take.named(n: Ar.Named, ps: List<&2, Ar.Prop>, ss: List<&2, Ar.Seen>, pre: List<&2, Ar.Record>, +k: String, v: Ar.Val) -> Ar.Step:
  match n:
    case Ar.NRefused{j, x}:
      Ar.StepNo{Ar.Refused{j, x}}
    case Ar.NUnknown{j, ns}:
      Ar.StepNo{Ar.Unknown{j, ns}}
    case Ar.NAs{+c}:
      take.free(taken(c, ss), c, ps, pre, k, v)

def take.key(sc: Ar.Schema, d: Ar.Dialect, ss: List<&2, Ar.Seen>, pre: List<&2, Ar.Record>, +k: String, v: Ar.Val) -> Ar.Step:
  match sc:
    case Ar.Schema{+ps, cl}:
      take.named(name(Ar.Schema{ps, cl}, d, k), ps, ss, pre, k, v)

def take.decoded(sc: Ar.Schema, d: Ar.Dialect, ss: List<&2, Ar.Seen>, +sent: String, dm: Maybe<&2, String>, v: Ar.Val) -> Ar.Step:
  match dm:
    case None{}:
      take.key(sc, d, ss, Nil{}, sent, v)
    case Some{+p}:
      take.key(sc, d, ss, [Ar.RAlias{sent, p}], p, v)

# S1-S5 for one argument, the names in ss taken before it
def take(sc: Ar.Schema, d: Ar.Dialect, +ks: List<&2, String>, ss: List<&2, Ar.Seen>, a: Ar.Arg) -> Ar.Step:
  match a:
    case Ar.Arg{+k, m, v}:
      take.decoded(sc, d, ss, k, decoding(ks, k, m), v)

def walk.next(st: Ar.Step, ss: List<&2, Ar.Seen>) -> List<&2, Ar.Seen>:
  match st:
    case Ar.StepOk{o, r, s}:
      s <> ss
    case Ar.StepNo{x}:
      ss

def walk.cons(st: Ar.Step, rest: Ar.Verdict) -> Ar.Verdict:
  match st:
    case Ar.StepOk{o, r, s}:
      match rest:
        case Ar.Repaired{os, rs}:
          Ar.Repaired{o <> os, List.append(&2, Ar.Record, r, rs)}
        case Ar.Rejected{x}:
          Ar.Rejected{x}
    case Ar.StepNo{x}:
      Ar.Rejected{x}

def walk(args: List<&2, Ar.Arg>, +sc: Ar.Schema, +d: Ar.Dialect, +ks: List<&2, String>, +ss: List<&2, Ar.Seen>) -> Ar.Verdict:
  match args:
    case Nil{}:
      Ar.Repaired{Nil{}, Nil{}}
    case a <> t:
      +st = take(sc, d, ks, ss, a)
      walk.cons(st, walk(t, sc, d, ks, walk.next(st, ss)))

# S1-S5: the repair of a call
def repair(sc: Ar.Schema, d: Ar.Dialect, +args: List<&2, Ar.Arg>) -> Ar.Verdict:
  walk(args, sc, d, sent_keys(args), Nil{})
