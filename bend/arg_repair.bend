# arg_repair: charitable argument repair (omp ADR 0020; omp `validation.ts`
# `normalizeDoubleEncodedKeys`, `tryCoerceForExpectedTypes`): strict on a
# tool's contract, charitable on the model's dialect. Rust (eukhe-bend
# rules/arg_repair.rs, asked by eukhe-durable harness/tool/arguments.rs
# for every tool call and every kernel `fs.*` request) decodes the JSON and
# sends what it read; this decides, per sent argument in order:
#
# - its key: a key sent as a JSON string (Rust: decoded up to 3 layers) is
#   read as the decoded key, unless that key is sent too; a key the dialect
#   refuses refuses the call with the dialect's hint; an undeclared key that
#   is an alias is read as the alias's canonical name; any other undeclared
#   key of a closed schema refuses the call (naming the declared keys); two
#   arguments read as one name refuse the call;
# - its value: a value in another spelling of the declared `type` is read as
#   that type: a number or boolean for `string` is its JSON text; a string
#   for `boolean` is true for `true`, `yes`, `on`, `1` and false for `false`,
#   `no`, `off`, `0` (trimmed, any ASCII case); for `integer` an optional
#   sign and decimal digits within i64 (trimmed); for `number` Rust's f64
#   reading of the trimmed text; for `object` the object the trimmed text
#   spells when it opens with `{`; for `array` the array it spells when it
#   opens with `[`, else (items of type `string`) the one-item array of it;
# - one record per change: the decoded key, the alias read, the value read.
#
# Containers are opaque: Rust keeps every sent value and every reading;
# only the spelling facts cross the wire. A string's text is sent when it
# has at most 4,096 chars (longer: None, and it spells no boolean or
# integer). Pure: no IO, no @unsafe.

import Base

# What a string's trimmed text opens with, and whether Rust's JSON reader
# (with repair) reads it as a container of that bracket.
type Shape is Data:
  SPlain{}
  SBrace{obj: Bool}
  SBracket{arr: Bool}

# A sent value as the repair sees it: a number as the JSON text Rust writes
# for it; a string as its text (None past 4,096 chars), its f64 reading's
# JSON text and its shape; containers opaque.
type Val is Data:
  VNull{}
  VBool{b: Bool}
  VNum{text: String}
  VStr{text: Maybe<&2, String>, num: Maybe<&2, String>, shape: Shape}
  VArr{}
  VObj{}

# A declared argument: its name, its `type` and its `items.type` (each None
# when absent or no string).
type Prop is Data:
  Prop{name: String, kind: Maybe<&2, String>, items: Maybe<&2, String>}

# The tool's parameters: the declared arguments in order, and whether the
# schema is closed (`additionalProperties: false`).
type Schema is Data:
  Schema{props: List<&2, Prop>, closed: Bool}

# A key and a text: an alias and its canonical name, or a refused key and
# its hint.
type KV is Data:
  KV{key: String, text: String}

# The dialect a tool declares: aliases it accepts and keys it refuses.
type Dialect is Data:
  Dialect{aliases: List<&2, KV>, refused: List<&2, KV>}

# A sent argument: its key, the key with its JSON string encoding removed
# (None: not a JSON string), its value.
type Arg is Data:
  Arg{key: String, plain: Maybe<&2, String>, value: Val}

# A value read as the declared type: a boolean, a number's JSON text, a
# string, the one-item array of the sent string, the object or the array
# the sent string spells.
type To is Data:
  TBool{b: Bool}
  TNum{text: String}
  TStr{text: String}
  TOne{}
  TObj{}
  TArr{}

# A sent argument repaired: the name it is read as, and its value read as
# the declared type (None: the sent value kept).
type Out is Data:
  Out{key: String, to: Maybe<&2, To>}

# One applied repair.
type Record is Data:
  RAlias{from: String, to: String}
  RCoerce{key: String, from: Val, to: To}

# Why no repair makes the arguments valid.
type Refusal is Data:
  Refused{key: String, hint: String}
  Unknown{key: String, valid: List<&2, String>}
  Ambiguous{canonical: String, first: String, key: String}

type Verdict is Data:
  Repaired{outs: List<&2, Out>, records: List<&2, Record>}
  Rejected{refusal: Refusal}

# The declared `type` of a parameter.
type Ty is Data:
  KString{}
  KBoolean{}
  KInteger{}
  KNumber{}
  KObject{}
  KArray{}
  KOther{}

# What a key is read as, before the keys sent with it count: refused (the
# hint), unknown (the declared names), or a name.
type Named is Data:
  NRefused{hint: String}
  NUnknown{valid: List<&2, String>}
  NAs{name: String}

# A name read so far: the name and the key sent for it.
type Seen is Data:
  Seen{name: String, key: String}

# One argument decided: repaired (its out, its records, the name it took),
# or the call refused.
type Step is Data:
  StepOk{out: Out, records: List<&2, Record>, seen: Seen}
  StepNo{refusal: Refusal}

# Lookups
# -------

# k is one of ks
def has(+k: String, ks: List<&2, String>) -> Bool:
  match ks:
    case Nil{}:
      False{}
    case x <> t:
      Bool.or(String.eq(k, x), has(k, t))

def keys(args: List<&2, Arg>) -> List<&2, String>:
  match args:
    case Nil{}:
      Nil{}
    case a <> t:
      match a:
        case Arg{k, p, v}:
          k <> keys(t)

def names(ps: List<&2, Prop>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case p <> t:
      match p:
        case Prop{n, k, i}:
          n <> names(t)

def prop.at(b: Bool, p: Prop, r: Maybe<&2, Prop>) -> Maybe<&2, Prop>:
  match b:
    case True{}:
      Some{p}
    case False{}:
      r

# the first declared argument named k
def prop(+k: String, ps: List<&2, Prop>) -> Maybe<&2, Prop>:
  match ps:
    case Nil{}:
      None{}
    case p <> t:
      match p:
        case Prop{+n, i, j}:
          prop.at(String.eq(k, n), Prop{n, i, j}, prop(k, t))

def found(m: Maybe<&2, Prop>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{p}:
      True{}

def pick.at(b: Bool, x: String, r: Maybe<&2, String>) -> Maybe<&2, String>:
  match b:
    case True{}:
      Some{x}
    case False{}:
      r

# the text of the first entry for k (an alias's canonical name, a refused
# key's hint)
def lookup(+k: String, kvs: List<&2, KV>) -> Maybe<&2, String>:
  match kvs:
    case Nil{}:
      None{}
    case e <> t:
      match e:
        case KV{+x, c}:
          pick.at(String.eq(k, x), c, lookup(k, t))

# the key sent first for the name c
def first_of(+c: String, ss: List<&2, Seen>) -> Maybe<&2, String>:
  match ss:
    case Nil{}:
      None{}
    case s <> t:
      match s:
        case Seen{+n, k}:
          pick.at(String.eq(c, n), k, first_of(c, t))

# Keys
# ----

def decoded.of(drop: Bool, p: String) -> Maybe<&2, String>:
  match drop:
    case True{}:
      None{}
    case False{}:
      Some{p}

# the key a sent key is read as when it was a JSON string: its decoding,
# unless that is the key itself or a key sent too
def decoded(+ks: List<&2, String>, +sent: String, m: Maybe<&2, String>) -> Maybe<&2, String>:
  match m:
    case None{}:
      None{}
    case Some{+p}:
      decoded.of(Bool.or(String.eq(p, sent), has(p, ks)), p)

# Spellings
# ---------

def kind.of(t: String, s: Bool, b: Bool, i: Bool, n: Bool, o: Bool, a: Bool) -> Ty:
  match s:
    case True{}:
      KString{}
    case False{}:
      match b:
        case True{}:
          KBoolean{}
        case False{}:
          match i:
            case True{}:
              KInteger{}
            case False{}:
              match n:
                case True{}:
                  KNumber{}
                case False{}:
                  match o:
                    case True{}:
                      KObject{}
                    case False{}:
                      match a:
                        case True{}:
                          KArray{}
                        case False{}:
                          KOther{}

# the declared type named t
def kind(+t: String) -> Ty:
  kind.of(t, String.eq(t, "string"), String.eq(t, "boolean"), String.eq(t, "integer"), String.eq(t, "number"), String.eq(t, "object"), String.eq(t, "array"))

# a White_Space code point (Rust `char::is_whitespace`, which `str::trim`
# strips)
def ws.code(+x: U32) -> Bool:
  Bool.or(Bool.and(U32.is_ge(x, 9), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 133), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_ge(x, 8192), U32.is_le(x, 8202)), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), U32.is_eq(x, 12288)))))))))))

def ws(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      ws.code(x)

def lstrip.at(w: Bool, c: Char, t: String, r: String) -> String:
  match w:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading white space
def lstrip(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      lstrip.at(ws(c), c, t, lstrip(t))

# s without its leading and trailing white space
def trim(s: String) -> String:
  String.reverse(lstrip(String.reverse(lstrip(s))))

def lower.at(up: Bool, x: U32) -> U32:
  match up:
    case True{}:
      U32.add(x, 32)
    case False{}:
      x

def lower.code(+x: U32) -> U32:
  lower.at(Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90)), x)

# s with ASCII capitals in lower case
def lower(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      match c:
        case Chr{x}:
          SCon{Chr{lower.code(x)}, lower(t)}

def word.of(t: Bool, f: Bool) -> Maybe<&2, To>:
  match t:
    case True{}:
      Some{TBool{True{}}}
    case False{}:
      match f:
        case True{}:
          Some{TBool{False{}}}
        case False{}:
          None{}

# the boolean a lower-case word spells
def word(+w: String) -> Maybe<&2, To>:
  word.of(Bool.or(String.eq(w, "true"), Bool.or(String.eq(w, "yes"), Bool.or(String.eq(w, "on"), String.eq(w, "1")))), Bool.or(String.eq(w, "false"), Bool.or(String.eq(w, "no"), Bool.or(String.eq(w, "off"), String.eq(w, "0")))))

def is_digit(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.and(U32.is_ge(x, 48), U32.is_le(x, 57))

# every char of s is an ASCII digit
def digits(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(is_digit(c), digits(t))

def unzero.at(z: Bool, c: Char, t: String, r: String) -> String:
  match z:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading `0`s
def unzero(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      unzero.at(Char.is_eq(c, '0'), c, t, unzero(t))

def canon.fin(s: String) -> String:
  match s:
    case SNil{}:
      "0"
    case SCon{c, t}:
      SCon{c, t}

# digits without leading zeros; `0` for none
def canon(s: String) -> String:
  canon.fin(unzero(s))

# canonical digits a at most b: fewer digits, or as many and not after in
# order
def at_most(+a: String, +b: String) -> Bool:
  +la = String.length(a)
  +lb = String.length(b)
  Bool.or(Nat.is_lt(la, lb), Bool.and(Nat.is_eq(la, lb), String.is_le(a, b)))

def int.fit(ok: Bool, text: String) -> Maybe<&2, To>:
  match ok:
    case True{}:
      Some{TNum{text}}
    case False{}:
      None{}

def int.neg.at(zero: Bool, +c: String) -> Maybe<&2, To>:
  match zero:
    case True{}:
      int.fit(True{}, "0")
    case False{}:
      int.fit(at_most(c, "9223372036854775808"), SCon{'-', c})

def int.neg(+c: String) -> Maybe<&2, To>:
  int.neg.at(String.eq(c, "0"), c)

def int.sign(neg: Bool, +c: String) -> Maybe<&2, To>:
  match neg:
    case True{}:
      int.neg(c)
    case False{}:
      int.fit(at_most(c, "9223372036854775807"), c)

def int.digits.at(ok: Bool, neg: Bool, d: String) -> Maybe<&2, To>:
  match ok:
    case True{}:
      int.sign(neg, canon(d))
    case False{}:
      None{}

def int.digits(neg: Bool, +d: String) -> Maybe<&2, To>:
  int.digits.at(Bool.and(Bool.not(String.is_empty(d)), digits(d)), neg, d)

def int.signed(minus: Bool, plus: Bool, c: Char, t: String) -> Maybe<&2, To>:
  match minus:
    case True{}:
      int.digits(True{}, t)
    case False{}:
      match plus:
        case True{}:
          int.digits(False{}, t)
        case False{}:
          int.digits(False{}, SCon{c, t})

# the i64 a trimmed text spells (Rust `str::parse::<i64>`): an optional
# `+` or `-`, then at least one ASCII digit, within -2^63..2^63-1; its JSON
# text without leading zeros (`-0` is `0`)
def int(s: String) -> Maybe<&2, To>:
  match s:
    case SNil{}:
      None{}
    case SCon{+c, t}:
      int.signed(Char.is_eq(c, '-'), Char.is_eq(c, '+'), c, t)

def spell.bool(m: Maybe<&2, String>) -> Maybe<&2, To>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      word(lower(trim(s)))

def spell.int(m: Maybe<&2, String>) -> Maybe<&2, To>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      int(trim(s))

def spell.num(m: Maybe<&2, String>) -> Maybe<&2, To>:
  match m:
    case None{}:
      None{}
    case Some{x}:
      Some{TNum{x}}

def spell.obj(sh: Shape) -> Maybe<&2, To>:
  match sh:
    case SPlain{}:
      None{}
    case SBrace{o}:
      match o:
        case True{}:
          Some{TObj{}}
        case False{}:
          None{}
    case SBracket{a}:
      None{}

def spell.one.at(b: Bool) -> Maybe<&2, To>:
  match b:
    case True{}:
      Some{TOne{}}
    case False{}:
      None{}

def spell.one(it: Maybe<&2, String>) -> Maybe<&2, To>:
  match it:
    case None{}:
      None{}
    case Some{t}:
      spell.one.at(String.eq(t, "string"))

def spell.arr(sh: Shape, it: Maybe<&2, String>) -> Maybe<&2, To>:
  match sh:
    case SPlain{}:
      spell.one(it)
    case SBrace{o}:
      spell.one(it)
    case SBracket{a}:
      match a:
        case True{}:
          Some{TArr{}}
        case False{}:
          None{}

# a string read as the declared kind
def spell(k: Ty, it: Maybe<&2, String>, text: Maybe<&2, String>, num: Maybe<&2, String>, sh: Shape) -> Maybe<&2, To>:
  match k:
    case KString{}:
      None{}
    case KBoolean{}:
      spell.bool(text)
    case KInteger{}:
      spell.int(text)
    case KNumber{}:
      spell.num(num)
    case KObject{}:
      spell.obj(sh)
    case KArray{}:
      spell.arr(sh, it)
    case KOther{}:
      None{}

def bool_text(b: Bool) -> String:
  match b:
    case True{}:
      "true"
    case False{}:
      "false"

def as_text(k: Ty, text: String) -> Maybe<&2, To>:
  match k:
    case KString{}:
      Some{TStr{text}}
    case KBoolean{}:
      None{}
    case KInteger{}:
      None{}
    case KNumber{}:
      None{}
    case KObject{}:
      None{}
    case KArray{}:
      None{}
    case KOther{}:
      None{}

# v read as the declared kind k (items: the declared `items.type`)
def coerce.val(+k: Ty, it: Maybe<&2, String>, v: Val) -> Maybe<&2, To>:
  match v:
    case VNull{}:
      None{}
    case VBool{b}:
      as_text(k, bool_text(b))
    case VNum{x}:
      as_text(k, x)
    case VStr{t, n, sh}:
      spell(k, it, t, n, sh)
    case VArr{}:
      None{}
    case VObj{}:
      None{}

# v read as the declared argument p's type (none for an undeclared one or
# one with no `type`)
def coerce(p: Maybe<&2, Prop>, v: Val) -> Maybe<&2, To>:
  match p:
    case None{}:
      None{}
    case Some{q}:
      match q:
        case Prop{n, k, it}:
          match k:
            case None{}:
              None{}
            case Some{t}:
              coerce.val(kind(t), it, v)

# Names
# -----

def named.closed(dec: Bool, cl: Bool, +k: String, ps: List<&2, Prop>) -> Named:
  match dec:
    case True{}:
      NAs{k}
    case False{}:
      match cl:
        case True{}:
          NUnknown{names(ps)}
        case False{}:
          NAs{k}

def named.alias(al: Maybe<&2, String>, dec: Bool, cl: Bool, +k: String, ps: List<&2, Prop>) -> Named:
  match al:
    case Some{c}:
      match dec:
        case True{}:
          NAs{k}
        case False{}:
          NAs{c}
    case None{}:
      named.closed(dec, cl, k, ps)

def named.hint(h: Maybe<&2, String>, sc: Schema, as: List<&2, KV>, +k: String) -> Named:
  match h:
    case Some{x}:
      NRefused{x}
    case None{}:
      match sc:
        case Schema{+ps, cl}:
          named.alias(lookup(k, as), found(prop(k, ps)), cl, k, ps)

# what the key k is read as: a refused key refuses (its first hint); an
# undeclared alias is its first canonical name; a declared key is itself;
# another key is unknown to a closed schema, itself to an open one
def named(sc: Schema, d: Dialect, +k: String) -> Named:
  match d:
    case Dialect{as, rs}:
      named.hint(lookup(k, rs), sc, as, k)

# Steps
# -----

def rename(same: Bool, k: String, c: String) -> List<&2, Record>:
  match same:
    case True{}:
      Nil{}
    case False{}:
      [RAlias{k, c}]

def coerced(c: String, v: Val, to: Maybe<&2, To>) -> List<&2, Record>:
  match to:
    case None{}:
      Nil{}
    case Some{x}:
      [RCoerce{c, v, x}]

def step.ok(same: Bool, +c: String, +to: Maybe<&2, To>, r0: List<&2, Record>, +k: String, v: Val) -> Step:
  StepOk{Out{c, to}, List.append(&2, Record, r0, List.append(&2, Record, rename(same, k, c), coerced(c, v, to))), Seen{c, k}}

def step.first(f: Maybe<&2, String>, +c: String, ps: List<&2, Prop>, r0: List<&2, Record>, +k: String, +v: Val) -> Step:
  match f:
    case Some{x}:
      StepNo{Ambiguous{c, x, k}}
    case None{}:
      step.ok(String.eq(c, k), c, coerce(prop(c, ps), v), r0, k, v)

# the name c is read: refused when another key took it
def step.seen(+c: String, ps: List<&2, Prop>, ss: List<&2, Seen>, r0: List<&2, Record>, k: String, v: Val) -> Step:
  step.first(first_of(c, ss), c, ps, r0, k, v)

def step.named(n: Named, ps: List<&2, Prop>, ss: List<&2, Seen>, r0: List<&2, Record>, +k: String, v: Val) -> Step:
  match n:
    case NRefused{x}:
      StepNo{Refused{k, x}}
    case NUnknown{ns}:
      StepNo{Unknown{k, ns}}
    case NAs{c}:
      step.seen(c, ps, ss, r0, k, v)

def step.key(sc: Schema, d: Dialect, ss: List<&2, Seen>, r0: List<&2, Record>, +k: String, v: Val) -> Step:
  match sc:
    case Schema{+ps, cl}:
      step.named(named(Schema{ps, cl}, d, k), ps, ss, r0, k, v)

def step.read(sc: Schema, d: Dialect, ss: List<&2, Seen>, +sent: String, dm: Maybe<&2, String>, v: Val) -> Step:
  match dm:
    case None{}:
      step.key(sc, d, ss, Nil{}, sent, v)
    case Some{+p}:
      step.key(sc, d, ss, [RAlias{sent, p}], p, v)

# one sent argument decided, the names in ss read before it (ks: every
# sent key)
def step(sc: Schema, d: Dialect, +ks: List<&2, String>, ss: List<&2, Seen>, a: Arg) -> Step:
  match a:
    case Arg{+k, m, v}:
      step.read(sc, d, ss, k, decoded(ks, k, m), v)

# The repair
# ----------

def seen.next(st: Step, ss: List<&2, Seen>) -> List<&2, Seen>:
  match st:
    case StepOk{o, r, s}:
      s <> ss
    case StepNo{x}:
      ss

def go.cons(st: Step, rest: Verdict) -> Verdict:
  match st:
    case StepOk{o, r, s}:
      match rest:
        case Repaired{os, rs}:
          Repaired{o <> os, List.append(&2, Record, r, rs)}
        case Rejected{x}:
          Rejected{x}
    case StepNo{x}:
      Rejected{x}

def go(args: List<&2, Arg>, +sc: Schema, +d: Dialect, +ks: List<&2, String>, +ss: List<&2, Seen>) -> Verdict:
  match args:
    case Nil{}:
      Repaired{Nil{}, Nil{}}
    case a <> t:
      +st = step(sc, d, ks, ss, a)
      go.cons(st, go(t, sc, d, ks, seen.next(st, ss)))

# the arguments args in the dialect d of the schema sc: one out per sent
# argument, in order, and one record per change; or the first refusal
def repair(sc: Schema, d: Dialect, +args: List<&2, Arg>) -> Verdict:
  go(args, sc, d, keys(args), Nil{})
