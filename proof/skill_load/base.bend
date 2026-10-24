# eukhe: lemmas the proofs of area skill_load share: the code's checks are
# the laws' (one lemma per function, by induction where it recurses), the
# entry's reader answers what the laws' reader answers, and a string that
# may be missing reads back.

import Base
import ../../bend/ffi_skill_load.bend as FSk
import ../../bend/skill_load.bend as Sk
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/skill_load.bend as SkillLoad
import ../../laws/wire.bend as Wire

# Logic
# -----

def sl.if_none(-A: Data, m: Maybe<&2, A>, G: Type) -> Type:
  match m:
    case None{}:
      G
    case Some{x}:
      Unit

def sl.some_none(-A: Data, -x: A, -G: Type, e: {Some{x} == None{} : Maybe<&2, A>}) -> G:
  %e : sl.if_none(A, _, G)
  Unit{}

# Chars and strings
# -----------------

def sl.ws(c: Char) -> {Sk.ws(c) == SkillLoad.ws_spec(c) : Bool}:
  match c:
    case Chr{x}:
      {==}

def sl.blank(s: String) -> {Sk.blank(s) == SkillLoad.blank_spec(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %sl.blank(t) : {Bool.and(Sk.ws(c), Sk.blank(t)) == Bool.and(SkillLoad.ws_spec(c), _) : Bool}
      %sl.ws(c) : {Bool.and(Sk.ws(c), Sk.blank(t)) == Bool.and(_, Sk.blank(t)) : Bool}
      {==}

def sl.utf8.code(a: Bool, b: Bool, c: Bool) -> {Sk.utf8.code(a, b, c) == SkillLoad.utf8_spec.code(a, b, c) : Nat}:
  match a b c:
    case True{} _ _:
      {==}
    case False{} True{} _:
      {==}
    case False{} False{} True{}:
      {==}
    case False{} False{} False{}:
      {==}

def sl.utf8(c: Char) -> {Sk.utf8(c) == SkillLoad.utf8_spec(c) : Nat}:
  match c:
    case Chr{+x}:
      sl.utf8.code(U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536))

def sl.bytes(s: String, n: Nat) -> {Sk.bytes(s, n) == SkillLoad.bytes_spec(s, n) : Nat}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %sl.utf8(c) : {Sk.bytes(t, Nat.add(Sk.utf8(c), n)) == SkillLoad.bytes_spec(t, Nat.add(_, n)) : Nat}
      sl.bytes(t, Nat.add(Sk.utf8(c), n))

def sl.chars(s: String) -> {Sk.name.chars(s) == SkillLoad.name_ok(s) : Bool}:
  match s:
    case SNil{}:
      {==}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          %sl.chars(t) : {Sk.name.chars(SCon{Chr{x}, t}) == Bool.and(Bool.or(Bool.and(U32.is_le(97, x), U32.is_le(x, 122)), Bool.or(Bool.and(U32.is_le(48, x), U32.is_le(x, 57)), U32.is_eq(x, 45))), _) : Bool}
          {==}

def sl.when(b: Bool, x: String, xs: List<&2, String>) -> {Sk.when(b, x, xs) == SkillLoad.msg_if(b, x, xs) : List<&2, String>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sl.whens(b1: Bool, x1: String, b2: Bool, x2: String, b3: Bool, x3: String, b4: Bool, x4: String, b5: Bool, x5: String) -> {Sk.when(b1, x1, Sk.when(b2, x2, Sk.when(b3, x3, Sk.when(b4, x4, Sk.when(b5, x5, []))))) == SkillLoad.msg_if(b1, x1, SkillLoad.msg_if(b2, x2, SkillLoad.msg_if(b3, x3, SkillLoad.msg_if(b4, x4, SkillLoad.msg_if(b5, x5, []))))) : List<&2, String>}:
  match b1 b2 b3 b4 b5:
    case True{} True{} True{} True{} True{}:
      {==}
    case True{} True{} True{} True{} False{}:
      {==}
    case True{} True{} True{} False{} True{}:
      {==}
    case True{} True{} True{} False{} False{}:
      {==}
    case True{} True{} False{} True{} True{}:
      {==}
    case True{} True{} False{} True{} False{}:
      {==}
    case True{} True{} False{} False{} True{}:
      {==}
    case True{} True{} False{} False{} False{}:
      {==}
    case True{} False{} True{} True{} True{}:
      {==}
    case True{} False{} True{} True{} False{}:
      {==}
    case True{} False{} True{} False{} True{}:
      {==}
    case True{} False{} True{} False{} False{}:
      {==}
    case True{} False{} False{} True{} True{}:
      {==}
    case True{} False{} False{} True{} False{}:
      {==}
    case True{} False{} False{} False{} True{}:
      {==}
    case True{} False{} False{} False{} False{}:
      {==}
    case False{} True{} True{} True{} True{}:
      {==}
    case False{} True{} True{} True{} False{}:
      {==}
    case False{} True{} True{} False{} True{}:
      {==}
    case False{} True{} True{} False{} False{}:
      {==}
    case False{} True{} False{} True{} True{}:
      {==}
    case False{} True{} False{} True{} False{}:
      {==}
    case False{} True{} False{} False{} True{}:
      {==}
    case False{} True{} False{} False{} False{}:
      {==}
    case False{} False{} True{} True{} True{}:
      {==}
    case False{} False{} True{} True{} False{}:
      {==}
    case False{} False{} True{} False{} True{}:
      {==}
    case False{} False{} True{} False{} False{}:
      {==}
    case False{} False{} False{} True{} True{}:
      {==}
    case False{} False{} False{} True{} False{}:
      {==}
    case False{} False{} False{} False{} True{}:
      {==}
    case False{} False{} False{} False{} False{}:
      {==}

def sl.desc.go(e: Bool, +n: Nat) -> {Sk.desc.msgs.go(e, n) == SkillLoad.desc_msgs.go(e, n) : List<&2, String>}:
  match e:
    case True{}:
      {==}
    case False{}:
      sl.when(Nat.is_lt(1024n, n), String.concat(["description exceeds 1024 characters (", Nat.show(n), ")"]), [])

def sl.desc(+d: String) -> {Sk.desc.msgs(d) == SkillLoad.desc_msgs(d) : List<&2, String>}:
  %sl.blank(d) : {Sk.desc.msgs(d) == SkillLoad.desc_msgs.go(_, SkillLoad.bytes_spec(d, 0n)) : List<&2, String>}
  %sl.bytes(d, 0n) : {Sk.desc.msgs(d) == SkillLoad.desc_msgs.go(Sk.blank(d), _) : List<&2, String>}
  sl.desc.go(Sk.blank(d), Sk.bytes(d, 0n))

def sl.name(+name: String, +parent: String) -> {Sk.name.msgs(name, parent) == SkillLoad.name_msgs(name, parent) : List<&2, String>}:
  +n = Sk.bytes(name, 0n)
  %sl.bytes(name, 0n) : {Sk.name.msgs(name, parent) == SkillLoad.msg_if(Bool.not(String.eq(name, parent)), String.concat(["name \"", name, "\" does not match parent directory \"", parent, "\""]), SkillLoad.msg_if(Nat.is_lt(64n, _), String.concat(["name exceeds 64 characters (", Nat.show(_), ")"]), SkillLoad.msg_if(Bool.or(Bool.not(SkillLoad.name_ok(name)), String.is_empty(name)), "name contains invalid characters (must be lowercase a-z, 0-9, hyphens only)", SkillLoad.msg_if(Bool.or(String.starts_with(name, "-"), String.ends_with(name, "-")), "name must not start or end with a hyphen", SkillLoad.msg_if(String.contains(name, "--"), "name must not contain consecutive hyphens", []))))) : List<&2, String>}
  %sl.chars(name) : {Sk.name.msgs(name, parent) == SkillLoad.msg_if(Bool.not(String.eq(name, parent)), String.concat(["name \"", name, "\" does not match parent directory \"", parent, "\""]), SkillLoad.msg_if(Nat.is_lt(64n, n), String.concat(["name exceeds 64 characters (", Nat.show(n), ")"]), SkillLoad.msg_if(Bool.or(Bool.not(_), String.is_empty(name)), "name contains invalid characters (must be lowercase a-z, 0-9, hyphens only)", SkillLoad.msg_if(Bool.or(String.starts_with(name, "-"), String.ends_with(name, "-")), "name must not start or end with a hyphen", SkillLoad.msg_if(String.contains(name, "--"), "name must not contain consecutive hyphens", []))))) : List<&2, String>}
  sl.whens(Bool.not(String.eq(name, parent)), String.concat(["name \"", name, "\" does not match parent directory \"", parent, "\""]), Nat.is_lt(64n, n), String.concat(["name exceeds 64 characters (", Nat.show(n), ")"]), Bool.or(Bool.not(Sk.name.chars(name)), String.is_empty(name)), "name contains invalid characters (must be lowercase a-z, 0-9, hyphens only)", Bool.or(String.starts_with(name, "-"), String.ends_with(name, "-")), "name must not start or end with a hyphen", String.contains(name, "--"), "name must not contain consecutive hyphens")

def sl.items(xs: List<&2, String>, -rest: String) -> {FSk.put_strs.items(xs, rest) == SkillLoad.spell_strs(xs, rest) : String}:
  match xs:
    case Nil{}:
      {==}
    case +x <> t:
      %sl.items(t, rest) : {Wr.put_str(x, FSk.put_strs.items(t, rest)) == Wr.put_str(x, _) : String}
      {==}

# the entry's reply to a skill is the laws'
def sl.checked(+name: String, +parent: String, +d: String) -> {FSk.put_checked(Sk.check.go(name, parent, d)) == SkillLoad.spell_skill(name, parent, d) : String}:
  +ms = List.append(&2, String, Sk.desc.msgs(d), Sk.name.msgs(name, parent))
  %sl.blank(d) : {FSk.put_checked(Sk.check.go(name, parent, d)) == Wr.put_bool(Bool.not(_), Wr.put_str(name, Wr.put_nat(List.length(&2, String, List.append(&2, String, SkillLoad.desc_msgs(d), SkillLoad.name_msgs(name, parent))), SkillLoad.spell_strs(List.append(&2, String, SkillLoad.desc_msgs(d), SkillLoad.name_msgs(name, parent)), "")))) : String}
  %sl.desc(d) : {FSk.put_checked(Sk.check.go(name, parent, d)) == Wr.put_bool(Bool.not(Sk.blank(d)), Wr.put_str(name, Wr.put_nat(List.length(&2, String, List.append(&2, String, _, SkillLoad.name_msgs(name, parent))), SkillLoad.spell_strs(List.append(&2, String, _, SkillLoad.name_msgs(name, parent)), "")))) : String}
  %sl.name(name, parent) : {FSk.put_checked(Sk.check.go(name, parent, d)) == Wr.put_bool(Bool.not(Sk.blank(d)), Wr.put_str(name, Wr.put_nat(List.length(&2, String, List.append(&2, String, Sk.desc.msgs(d), _)), SkillLoad.spell_strs(List.append(&2, String, Sk.desc.msgs(d), _), "")))) : String}
  %sl.items(ms, "") : {FSk.put_checked(Sk.check.go(name, parent, d)) == Wr.put_bool(Bool.not(Sk.blank(d)), Wr.put_str(name, Wr.put_nat(List.length(&2, String, ms), _))) : String}
  {==}

def sl.name_of.pick(e: Bool, n: String, parent: String) -> {Sk.name.pick(e, n, parent) == SkillLoad.name_spec.pick(e, n, parent) : String}:
  match e:
    case True{}:
      {==}
    case False{}:
      {==}

def sl.name_of(+m: Maybe<&2, String>, +parent: String) -> {Sk.name.of(m, parent) == SkillLoad.name_spec(m, parent) : String}:
  match m:
    case None{}:
      {==}
    case Some{+n}:
      sl.name_of.pick(String.is_empty(n), n, parent)

def sl.text(m: Maybe<&2, String>) -> {Sk.text.of(m) == SkillLoad.or_empty(m) : String}:
  match m:
    case None{}:
      {==}
    case Some{d}:
      {==}

# the entry's reply to a skill request is the laws'
def sl.skill(+n: Maybe<&2, String>, +p: String, +d: Maybe<&2, String>) -> {FSk.put_checked(Sk.check(n, p, d)) == SkillLoad.spell_skill(SkillLoad.name_spec(n, p), p, SkillLoad.or_empty(d)) : String}:
  %sl.name_of(n, p) : {FSk.put_checked(Sk.check.go(Sk.name.of(n, p), p, Sk.text.of(d))) == SkillLoad.spell_skill(_, p, SkillLoad.or_empty(d)) : String}
  %sl.text(d) : {FSk.put_checked(Sk.check.go(Sk.name.of(n, p), p, Sk.text.of(d))) == SkillLoad.spell_skill(Sk.name.of(n, p), p, _) : String}
  sl.checked(Sk.name.of(n, p), p, Sk.text.of(d))

# Trim, the first line, the cut
# -----------------------------

def sl.trim.go(t: String, b: Bool, c: Char) -> {Sk.trim.go(t, b, c) == SkillLoad.trim_spec.go(t, b, c) : String}:
  match t:
    case SNil{}:
      match b:
        case True{}:
          {==}
        case False{}:
          {==}
    case SCon{+d, r}:
      match b:
        case True{}:
          %sl.ws(d) : {Sk.trim.go(r, Sk.ws(d), d) == SkillLoad.trim_spec.go(r, _, d) : String}
          sl.trim.go(r, Sk.ws(d), d)
        case False{}:
          {==}

def sl.trim.start(s: String) -> {Sk.trim.start(s) == SkillLoad.trim_spec.start(s) : String}:
  match s:
    case SNil{}:
      {==}
    case SCon{+c, t}:
      %sl.ws(c) : {Sk.trim.go(t, Sk.ws(c), c) == SkillLoad.trim_spec.go(t, _, c) : String}
      sl.trim.go(t, Sk.ws(c), c)

def sl.trim(+s: String) -> {Sk.trim(s) == SkillLoad.trim_spec(s) : String}:
  %sl.trim.start(s) : {Sk.trim(s) == String.reverse(SkillLoad.trim_spec.start(String.reverse(_))) : String}
  %sl.trim.start(String.reverse(Sk.trim.start(s))) : {Sk.trim(s) == String.reverse(_) : String}
  {==}

def sl.first.go(ls: List<&2, String>, b: Bool, l: String) -> {Sk.first.go(ls, b, l) == SkillLoad.first_spec.go(ls, b, l) : String}:
  match ls:
    case Nil{}:
      match b:
        case True{}:
          {==}
        case False{}:
          sl.trim(l)
    case +m <> rest:
      match b:
        case True{}:
          %sl.blank(m) : {Sk.first.go(rest, Sk.blank(m), m) == SkillLoad.first_spec.go(rest, _, m) : String}
          sl.first.go(rest, Sk.blank(m), m)
        case False{}:
          sl.trim(l)

def sl.first(ls: List<&2, String>) -> {Sk.first(ls) == SkillLoad.first_spec(ls) : String}:
  match ls:
    case Nil{}:
      {==}
    case +l <> rest:
      %sl.blank(l) : {Sk.first.go(rest, Sk.blank(l), l) == SkillLoad.first_spec.go(rest, _, l) : String}
      sl.first.go(rest, Sk.blank(l), l)

def sl.cut.if(b: Bool, l: String) -> {Sk.cut.if(b, l) == SkillLoad.cut_spec.if(b, l) : String}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def sl.summary.pick(e: Bool, d: String, +body: String) -> {Sk.summary.pick(e, d, body) == SkillLoad.summary_spec.pick(e, d, body) : String}:
  match e:
    case True{}:
      +l = Sk.first(String.lines(body))
      %sl.first(String.lines(body)) : {Sk.cut(l) == SkillLoad.cut_spec(_) : String}
      sl.cut.if(Nat.is_lt(60n, String.length(l)), l)
    case False{}:
      {==}

# a template's description is the laws'
def sl.summary(+m: Maybe<&2, String>, +body: String) -> {Sk.summary(m, body) == SkillLoad.summary_spec(m, body) : String}:
  %sl.text(m) : {Sk.summary.go(Sk.text.of(m), body) == SkillLoad.summary_spec.go(_, body) : String}
  +d = Sk.text.of(m)
  sl.summary.pick(String.is_empty(d), d, body)

# The reader
# ----------

def sl.text_some(r: Wr.Dec<String>) -> {SkillLoad.read_text.some(r) == FSk.get_text.some(r) : Wr.Dec<Maybe<&2, String>>}:
  match r:
    case Wr.Got{x, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sl.text_tag(t: Nat, s: String) -> {SkillLoad.read_text.tag(t, s) == FSk.get_text.tag(t, s) : Wr.Dec<Maybe<&2, String>>}:
  match t:
    case 0n:
      {==}
    case 1n:
      sl.text_some(Wr.get_str(s))
    case 2n+p:
      {==}

def sl.text_go(r: Wr.Dec<Nat>) -> {SkillLoad.read_text.go(r) == FSk.get_text.go(r) : Wr.Dec<Maybe<&2, String>>}:
  match r:
    case Wr.Got{t, s}:
      sl.text_tag(t, s)
    case Wr.Bad{}:
      {==}

def sl.read_text(s: String) -> {SkillLoad.read_text(s) == FSk.get_text(s) : Wr.Dec<Maybe<&2, String>>}:
  sl.text_go(Wr.get_nat(s))

def sl.skill_desc(n: Maybe<&2, String>, p: String, r: Wr.Dec<Maybe<&2, String>>) -> {SkillLoad.read_skill.desc(n, p, r) == FSk.get_skill.desc(n, p, r) : Wr.Dec<Sk.Ask>}:
  match r:
    case Wr.Got{d, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sl.skill_parent(n: Maybe<&2, String>, r: Wr.Dec<String>) -> {SkillLoad.read_skill.parent(n, r) == FSk.get_skill.parent(n, r) : Wr.Dec<Sk.Ask>}:
  match r:
    case Wr.Got{+p, +s}:
      %sl.read_text(s) : {SkillLoad.read_skill.desc(n, p, SkillLoad.read_text(s)) == FSk.get_skill.desc(n, p, _) : Wr.Dec<Sk.Ask>}
      sl.skill_desc(n, p, SkillLoad.read_text(s))
    case Wr.Bad{}:
      {==}

def sl.read_skill(r: Wr.Dec<Maybe<&2, String>>) -> {SkillLoad.read_skill(r) == FSk.get_skill(r) : Wr.Dec<Sk.Ask>}:
  match r:
    case Wr.Got{n, s}:
      sl.skill_parent(n, Wr.get_str(s))
    case Wr.Bad{}:
      {==}

def sl.template_body(d: Maybe<&2, String>, r: Wr.Dec<String>) -> {SkillLoad.read_template.body(d, r) == FSk.get_template.body(d, r) : Wr.Dec<Sk.Ask>}:
  match r:
    case Wr.Got{b, s}:
      {==}
    case Wr.Bad{}:
      {==}

def sl.read_template(r: Wr.Dec<Maybe<&2, String>>) -> {SkillLoad.read_template(r) == FSk.get_template(r) : Wr.Dec<Sk.Ask>}:
  match r:
    case Wr.Got{d, s}:
      sl.template_body(d, Wr.get_str(s))
    case Wr.Bad{}:
      {==}

def sl.ask_tag(t: Nat, +s: String) -> {SkillLoad.read_ask.tag(t, s) == FSk.get_ask.tag(t, s) : Wr.Dec<Sk.Ask>}:
  match t:
    case 0n:
      %sl.read_text(s) : {SkillLoad.read_skill(SkillLoad.read_text(s)) == FSk.get_skill(_) : Wr.Dec<Sk.Ask>}
      sl.read_skill(SkillLoad.read_text(s))
    case 1n:
      %sl.read_text(s) : {SkillLoad.read_template(SkillLoad.read_text(s)) == FSk.get_template(_) : Wr.Dec<Sk.Ask>}
      sl.read_template(SkillLoad.read_text(s))
    case 2n+p:
      {==}

# the entry reads every input as the laws' reader does
def sl.ask(r: Wr.Dec<Nat>) -> {SkillLoad.read_ask.go(r) == FSk.get_ask.go(r) : Wr.Dec<Sk.Ask>}:
  match r:
    case Wr.Got{t, s}:
      sl.ask_tag(t, s)
    case Wr.Bad{}:
      {==}

# a string that may be missing reads back, whatever follows it
def sl.text_rt(m: Maybe<&2, String>, +rest: String, h: {SkillLoad.text_fits(m) == True{} : Bool}) -> {Wr.Got{m, rest} == FSk.get_text(SkillLoad.spell_text(m, rest)) : Wr.Dec<Maybe<&2, String>>}:
  match m:
    case None{}:
      {==}
    case Some{+x}:
      %Equal.sym(Wr.Dec<String>, Wr.get_str(Wr.put_str(x, rest)), Wr.Got{x, rest}, Wire.wire_str_round_trip(x, rest, h)) : {Wr.Got{Some{x}, rest} == FSk.get_text.some(_) : Wr.Dec<Maybe<&2, String>>}
      {==}
