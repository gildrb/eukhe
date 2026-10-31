# eukhe: the proof of LAW arg_repair_coerce_spec
#
# PROOF: the model's spelling helpers and the spec's compute the same
# answer on every input: each pair is equal by induction over the string
# (cs.lstrip, cs.lower, cs.digits, cs.unzero) or by cases on the Bool it
# branches on (cs.*_at); the reading of each declared type then matches
# case by case (cs.val).

import Base
import ../../bend/arg_repair.bend as Ar
import ../../spec/harness/arguments.bend as ArgSpec
import ../../laws/arg_repair.bend as ArgRepair

# Text
# ----

def cs.lstrip_at(w: Bool, c: Char, t: String, -r: String) -> {Ar.lstrip.at(w, c, t, r) == ArgSpec.lead.at(w, c, t, r) : String}:
  match w:
    case True{}:
      {==}
    case False{}:
      {==}

def cs.ws(c: Char) -> {Ar.ws(c) == ArgSpec.white(c) : Bool}:
  match c:
    case Chr{x}:
      {==}

def cs.lstrip(s: String) -> {Ar.lstrip(s) == ArgSpec.lead(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %cs.lstrip(t) : {Ar.lstrip.at(Ar.ws(c), c, t, Ar.lstrip(t)) == ArgSpec.lead.at(ArgSpec.white(c), c, t, _) : String}
      %cs.ws(c) : {Ar.lstrip.at(Ar.ws(c), c, t, Ar.lstrip(t)) == ArgSpec.lead.at(_, c, t, Ar.lstrip(t)) : String}
      cs.lstrip_at(Ar.ws(c), c, t, Ar.lstrip(t))

def cs.trim(+s: String) -> {Ar.trim(s) == ArgSpec.trimmed(s) : String}:
  %cs.lstrip(s) : {String.reverse(Ar.lstrip(String.reverse(Ar.lstrip(s)))) == String.reverse(ArgSpec.lead(String.reverse(_))) : String}
  %cs.lstrip(String.reverse(Ar.lstrip(s))) : {String.reverse(Ar.lstrip(String.reverse(Ar.lstrip(s)))) == String.reverse(_) : String}
  {==}

def cs.lower_at(b: Bool, x: U32) -> {Ar.lower.at(b, x) == ArgSpec.small.at(b, x) : U32}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cs.lower(s: String) -> {Ar.lower(s) == ArgSpec.small(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          %cs.lower(t) : {SCon{Chr{Ar.lower.code(x)}, Ar.lower(t)} == SCon{Chr{ArgSpec.small.at(Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90)), x)}, _} : String}
          %cs.lower_at(Bool.and(U32.is_ge(x, 65), U32.is_le(x, 90)), x) : {SCon{Chr{Ar.lower.code(x)}, Ar.lower(t)} == SCon{Chr{_}, Ar.lower(t)} : String}
          {==}

def cs.or_false(b: Bool) -> {b == Bool.or(b, False{}) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cs.word_of(t: Bool, f: Bool) -> {Ar.word.of(t, f) == ArgSpec.truth.of(t, f) : Maybe<&2, Ar.To>}:
  match t:
    case True{}:
      {==}
    case False{}:
      match f:
        case True{}:
          {==}
        case False{}:
          {==}

def cs.word(+w: String) -> {Ar.word(w) == ArgSpec.truth(w) : Maybe<&2, Ar.To>}:
  %cs.or_false(String.eq(w, "1")) : {Ar.word(w) == ArgSpec.truth.of(Bool.or(String.eq(w, "true"), Bool.or(String.eq(w, "yes"), Bool.or(String.eq(w, "on"), _))), ArgSpec.member(w, ["false", "no", "off", "0"])) : Maybe<&2, Ar.To>}
  %cs.or_false(String.eq(w, "0")) : {Ar.word(w) == ArgSpec.truth.of(Bool.or(String.eq(w, "true"), Bool.or(String.eq(w, "yes"), Bool.or(String.eq(w, "on"), String.eq(w, "1")))), Bool.or(String.eq(w, "false"), Bool.or(String.eq(w, "no"), Bool.or(String.eq(w, "off"), _)))) : Maybe<&2, Ar.To>}
  cs.word_of(Bool.or(String.eq(w, "true"), Bool.or(String.eq(w, "yes"), Bool.or(String.eq(w, "on"), String.eq(w, "1")))), Bool.or(String.eq(w, "false"), Bool.or(String.eq(w, "no"), Bool.or(String.eq(w, "off"), String.eq(w, "0")))))

# Integers
# --------

def cs.digits(s: String) -> {Ar.digits(s) == ArgSpec.all_digits(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          %cs.digits(t) : {Bool.and(Ar.is_digit(Chr{x}), Ar.digits(t)) == Bool.and(ArgSpec.digit(Chr{x}), _) : Bool}
          {==}

def cs.unzero_at(z: Bool, c: Char, t: String, -r: String) -> {Ar.unzero.at(z, c, t, r) == ArgSpec.nozero.at(z, c, t, r) : String}:
  match z:
    case True{}:
      {==}
    case False{}:
      {==}

def cs.unzero(s: String) -> {Ar.unzero(s) == ArgSpec.nozero(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +t}:
      %cs.unzero(t) : {Ar.unzero.at(Char.is_eq(c, '0'), c, t, Ar.unzero(t)) == ArgSpec.nozero.at(Char.is_eq(c, '0'), c, t, _) : String}
      cs.unzero_at(Char.is_eq(c, '0'), c, t, Ar.unzero(t))

def cs.canon_fin(s: String) -> {Ar.canon.fin(s) == ArgSpec.plain_digits.fin(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      {==}

def cs.canon(+s: String) -> {Ar.canon(s) == ArgSpec.plain_digits(s) : String}:
  %cs.unzero(s) : {Ar.canon.fin(Ar.unzero(s)) == ArgSpec.plain_digits.fin(_) : String}
  cs.canon_fin(Ar.unzero(s))

def cs.fit(ok: Bool, -x: String) -> {Ar.int.fit(ok, x) == ArgSpec.integer.in(ok, x) : Maybe<&2, Ar.To>}:
  match ok:
    case True{}:
      {==}
    case False{}:
      {==}

def cs.neg_at(z: Bool, +c: String) -> {Ar.int.neg.at(z, c) == ArgSpec.integer.minus.at(z, c) : Maybe<&2, Ar.To>}:
  match z:
    case True{}:
      {==}
    case False{}:
      cs.fit(Ar.at_most(c, "9223372036854775808"), SCon{'-', c})

def cs.sign(neg: Bool, +c: String) -> {Ar.int.sign(neg, c) == ArgSpec.integer.signed(neg, c) : Maybe<&2, Ar.To>}:
  match neg:
    case True{}:
      cs.neg_at(String.eq(c, "0"), c)
    case False{}:
      cs.fit(Ar.at_most(c, "9223372036854775807"), c)

def cs.digits_at(ok: Bool, neg: Bool, +d: String) -> {Ar.int.digits.at(ok, neg, d) == ArgSpec.integer.body.at(ok, neg, d) : Maybe<&2, Ar.To>}:
  match ok:
    case True{}:
      %cs.canon(d) : {Ar.int.sign(neg, Ar.canon(d)) == ArgSpec.integer.signed(neg, _) : Maybe<&2, Ar.To>}
      cs.sign(neg, Ar.canon(d))
    case False{}:
      {==}

def cs.body(neg: Bool, +d: String) -> {Ar.int.digits(neg, d) == ArgSpec.integer.body(neg, d) : Maybe<&2, Ar.To>}:
  %cs.digits(d) : {Ar.int.digits.at(Bool.and(Bool.not(String.is_empty(d)), Ar.digits(d)), neg, d) == ArgSpec.integer.body.at(Bool.and(Bool.not(String.is_empty(d)), _), neg, d) : Maybe<&2, Ar.To>}
  cs.digits_at(Bool.and(Bool.not(String.is_empty(d)), Ar.digits(d)), neg, d)

def cs.signed(minus: Bool, plus: Bool, c: Char, t: String) -> {Ar.int.signed(minus, plus, c, t) == ArgSpec.integer.lead(minus, plus, c, t) : Maybe<&2, Ar.To>}:
  match minus:
    case True{}:
      cs.body(True{}, t)
    case False{}:
      match plus:
        case True{}:
          cs.body(False{}, t)
        case False{}:
          cs.body(False{}, SCon{c, t})

def cs.int(s: String) -> {Ar.int(s) == ArgSpec.integer(s) : Maybe<&2, Ar.To>}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      cs.signed(Char.is_eq(c, '-'), Char.is_eq(c, '+'), c, t)

# Readings
# --------

def cs.bool(m: Maybe<&2, String>) -> {Ar.spell.bool(m) == ArgSpec.read_bool(m) : Maybe<&2, Ar.To>}:
  match m:
    case None{}:
      {==}
    case Some{+s}:
      %cs.trim(s) : {Ar.word(Ar.lower(Ar.trim(s))) == ArgSpec.truth(ArgSpec.small(_)) : Maybe<&2, Ar.To>}
      %cs.lower(Ar.trim(s)) : {Ar.word(Ar.lower(Ar.trim(s))) == ArgSpec.truth(_) : Maybe<&2, Ar.To>}
      cs.word(Ar.lower(Ar.trim(s)))

def cs.integer(m: Maybe<&2, String>) -> {Ar.spell.int(m) == ArgSpec.read_int(m) : Maybe<&2, Ar.To>}:
  match m:
    case None{}:
      {==}
    case Some{+s}:
      %cs.trim(s) : {Ar.int(Ar.trim(s)) == ArgSpec.integer(_) : Maybe<&2, Ar.To>}
      cs.int(Ar.trim(s))

def cs.num(m: Maybe<&2, String>) -> {Ar.spell.num(m) == ArgSpec.read_num(m) : Maybe<&2, Ar.To>}:
  match m:
    case None{}:
      {==}
    case Some{x}:
      {==}

def cs.obj(sh: Ar.Shape) -> {Ar.spell.obj(sh) == ArgSpec.read_obj(sh) : Maybe<&2, Ar.To>}:
  match sh:
    case Ar.SPlain{}:
      {==}
    case Ar.SBrace{o}:
      match o:
        case True{}:
          {==}
        case False{}:
          {==}
    case Ar.SBracket{a}:
      {==}

def cs.one_at(b: Bool) -> {Ar.spell.one.at(b) == ArgSpec.lone.at(b) : Maybe<&2, Ar.To>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def cs.one(it: Maybe<&2, String>) -> {Ar.spell.one(it) == ArgSpec.lone(it) : Maybe<&2, Ar.To>}:
  match it:
    case None{}:
      {==}
    case Some{t}:
      cs.one_at(String.eq(t, "string"))

def cs.arr(sh: Ar.Shape, it: Maybe<&2, String>) -> {Ar.spell.arr(sh, it) == ArgSpec.read_arr(sh, it) : Maybe<&2, Ar.To>}:
  match sh:
    case Ar.SPlain{}:
      cs.one(it)
    case Ar.SBrace{o}:
      cs.one(it)
    case Ar.SBracket{a}:
      match a:
        case True{}:
          {==}
        case False{}:
          {==}

def cs.spell(k: Ar.Ty, it: Maybe<&2, String>, t: Maybe<&2, String>, n: Maybe<&2, String>, sh: Ar.Shape) -> {Ar.spell(k, it, t, n, sh) == ArgSpec.read_str(k, it, t, n, sh) : Maybe<&2, Ar.To>}:
  match k:
    case Ar.KString{}:
      {==}
    case Ar.KBoolean{}:
      cs.bool(t)
    case Ar.KInteger{}:
      cs.integer(t)
    case Ar.KNumber{}:
      cs.num(n)
    case Ar.KObject{}:
      cs.obj(sh)
    case Ar.KArray{}:
      cs.arr(sh, it)
    case Ar.KOther{}:
      {==}

def cs.text(k: Ar.Ty, x: String) -> {Ar.as_text(k, x) == ArgSpec.text_of(k, x) : Maybe<&2, Ar.To>}:
  match k:
    case Ar.KString{}:
      {==}
    case Ar.KBoolean{}:
      {==}
    case Ar.KInteger{}:
      {==}
    case Ar.KNumber{}:
      {==}
    case Ar.KObject{}:
      {==}
    case Ar.KArray{}:
      {==}
    case Ar.KOther{}:
      {==}

def cs.bool_text(k: Ar.Ty, b: Bool) -> {Ar.as_text(k, Ar.bool_text(b)) == ArgSpec.text_of(k, ArgSpec.bool_word(b)) : Maybe<&2, Ar.To>}:
  match b:
    case True{}:
      cs.text(k, "true")
    case False{}:
      cs.text(k, "false")

def cs.val(+k: Ar.Ty, it: Maybe<&2, String>, v: Ar.Val) -> {Ar.coerce.val(k, it, v) == ArgSpec.read_val(k, it, v) : Maybe<&2, Ar.To>}:
  match v:
    case Ar.VNull{}:
      {==}
    case Ar.VBool{b}:
      cs.bool_text(k, b)
    case Ar.VNum{x}:
      cs.text(k, x)
    case Ar.VStr{t, n, sh}:
      cs.spell(k, it, t, n, sh)
    case Ar.VArr{}:
      {==}
    case Ar.VObj{}:
      {==}

def cs.kind_of(t: String, s: Bool, b: Bool, i: Bool, n: Bool, o: Bool, a: Bool) -> {Ar.kind.of(t, s, b, i, n, o, a) == ArgSpec.kind.of(t, s, b, i, n, o, a) : Ar.Ty}:
  match s:
    case True{}:
      {==}
    case False{}:
      match b:
        case True{}:
          {==}
        case False{}:
          match i:
            case True{}:
              {==}
            case False{}:
              match n:
                case True{}:
                  {==}
                case False{}:
                  match o:
                    case True{}:
                      {==}
                    case False{}:
                      match a:
                        case True{}:
                          {==}
                        case False{}:
                          {==}

def cs.kind(+t: String) -> {Ar.kind(t) == ArgSpec.kind(t) : Ar.Ty}:
  cs.kind_of(t, String.eq(t, "string"), String.eq(t, "boolean"), String.eq(t, "integer"), String.eq(t, "number"), String.eq(t, "object"), String.eq(t, "array"))

def ArgRepair.arg_repair_coerce_spec(p, v):
  match p:
    case None{}:
      {==}
    case Some{q}:
      match q:
        case Ar.Prop{n, k, it}:
          match k:
            case None{}:
              {==}
            case Some{+t}:
              %cs.kind(t) : {Ar.coerce.val(Ar.kind(t), it, v) == ArgSpec.read_val(_, it, v) : Maybe<&2, Ar.To>}
              cs.val(Ar.kind(t), it, v)
