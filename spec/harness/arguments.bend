# harness (spec): charitable argument repair (omp ADR 0020): the
# requirement S1-S5 and the words the laws of area arg_repair
# (laws/arg_repair.bend, laws/arg_repair/coerce.bend) state it with: a
# call's sent keys, a key's decoding, the first text a list gives a key,
# the first declared argument of a name, the name a key read is read as.
# No law equals the repair to a function of this file: each law states one
# property of the shipped repair. A spec: the shipped code never calls it.
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

def key_read.of(dm: Maybe<&2, String>, k: String) -> String:
  match dm:
    case None{}:
      k
    case Some{p}:
      p

# S1: the key an argument is read as, ks the call's sent keys
def key_read(+ks: List<&2, String>, a: Ar.Arg) -> String:
  match a:
    case Ar.Arg{+k, p, v}:
      key_read.of(decoding(ks, k, p), k)

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

def name_of.at(dec: Bool, al: Maybe<&2, String>, k: String) -> String:
  match dec:
    case True{}:
      k
    case False{}:
      match al:
        case None{}:
          k
        case Some{c}:
          c

# S2: the name a key read k is read as when the call is repaired: k when
# it is declared or no alias names it, else its first alias's canonical
# name
def name_of(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +k: String) -> String:
  name_of.at(is_some(declared(k, ps)), first_text(k, als), k)

# S2: the names the arguments are read as, in order
def names(+ps: List<&2, Ar.Prop>, +als: List<&2, Ar.KV>, +ks: List<&2, String>, xs: List<&2, Ar.Arg>) -> List<&2, String>:
  match xs:
    case Nil{}:
      Nil{}
    case a <> t:
      name_of(ps, als, key_read(ks, a)) <> names(ps, als, ks, t)

# S3: no name of ns is one before it (taken: the names before them)
def fresh(ns: List<&2, String>, +taken: List<&2, String>) -> Bool:
  match ns:
    case Nil{}:
      True{}
    case +n <> t:
      Bool.and(Bool.not(member(n, taken)), fresh(t, n <> taken))

# S5: records
# -----------

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
