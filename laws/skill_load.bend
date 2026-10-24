# eukhe: the laws of area skill_load

import Base
import ../bend/skill_load.bend as Sk
import ../bend/ffi_skill_load.bend as FSk
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (L5) A skill file that fails to load is reported
# ------------------------------------------------
# bend/skill_load.bend: the skill and prompt-template loaders over their
# candidate files (`load`): each file loads, or a diagnostic names its
# path and error.

# LAW skill_failure_reported: every candidate file is loaded or named by a diagnostic
law skill_failure_reported:
  for cs: List<&2, Sk.Cand>
  for +c: Sk.Cand
  for i: Sk.In(c, cs)
  {Bool.or(Sk.listed(Sk.loaded(cs), Sk.Cand.path(c)), Sk.listed(Sk.named(Sk.diags(cs)), Sk.Cand.path(c))) == True{} : Bool}

# LAW skill_loaded_not_failed: of distinct candidates, no file both loads and fails
law skill_loaded_not_failed:
  for cs: List<&2, Sk.Cand>
  for +n: Nat
  for +d: {Sk.distinct(cs) == True{} : Bool}
  {Bool.and(Sk.listed(Sk.loaded(cs), n), Sk.listed(Sk.named(Sk.diags(cs)), n)) == False{} : Bool}

# the diagnostic of a candidate that does not load: kind 0 unreadable, 1
# malformed frontmatter, 2 no description
def diags_spec(cs: List<&2, Sk.Cand>) -> List<&2, Sk.Diag>:
  match cs:
    case Nil{}:
      Nil{}
    case Sk.Cand{p, o} <> rest:
      match o:
        case Sk.Good{}:
          diags_spec(rest)
        case Sk.Unreadable{}:
          Sk.Diag{p, 0n} <> diags_spec(rest)
        case Sk.Malformed{}:
          Sk.Diag{p, 1n} <> diags_spec(rest)
        case Sk.Incomplete{}:
          Sk.Diag{p, 2n} <> diags_spec(rest)

# LAW skill_diag_kinds: each candidate that does not load gets one diagnostic, in order, naming its path and why (0 unreadable, 1 malformed, 2 no description)
law skill_diag_kinds:
  for cs: List<&2, Sk.Cand>
  {Sk.diags(cs) == diags_spec(cs) : List<&2, Sk.Diag>}

# LAW skill_distinct_example: witness: candidates of two paths are distinct, two of one path are not (so skill_loaded_not_failed is not vacuous)
law skill_distinct_example:
  {Sk.distinct([Sk.Cand{0n, Sk.Good{}}, Sk.Cand{1n, Sk.Unreadable{}}]) == True{} : Bool} &
  {Sk.distinct([Sk.Cand{0n, Sk.Good{}}, Sk.Cand{0n, Sk.Malformed{}}]) == False{} : Bool}

# the paths of the candidates that load, in order
def loaded_spec(cs: List<&2, Sk.Cand>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case Sk.Cand{p, o} <> rest:
      match o:
        case Sk.Good{}:
          p <> loaded_spec(rest)
        case Sk.Unreadable{}:
          loaded_spec(rest)
        case Sk.Malformed{}:
          loaded_spec(rest)
        case Sk.Incomplete{}:
          loaded_spec(rest)

# LAW skill_loaded_exact: exactly the candidates that read well load, in order
law skill_loaded_exact:
  for cs: List<&2, Sk.Cand>
  {Sk.loaded(cs) == loaded_spec(cs) : List<&2, Nat>}

# LAW skill_in_first_example: witness: a candidate is in a list it heads (so skill_failure_reported is not vacuous)
law skill_in_first_example:
  exs i: Sk.In(Sk.Cand{0n, Sk.Good{}}, [Sk.Cand{0n, Sk.Good{}}])
  {Sk.Cand.path(Sk.Cand{0n, Sk.Good{}}) == 0n : Nat}

# LAW skill_in_later_example: witness: a candidate is in a list that holds it after another
law skill_in_later_example:
  exs i: Sk.In(Sk.Cand{1n, Sk.Unreadable{}}, [Sk.Cand{0n, Sk.Good{}}, Sk.Cand{1n, Sk.Unreadable{}}])
  {Sk.Cand.path(Sk.Cand{1n, Sk.Unreadable{}}) == 1n : Nat}

# (L5) The checks of a skill file and a template, and the entry Rust calls
# -----------------------------------------------------------------------
# crates/eukhe-core/src/skills: `load_skill_from_file` (the skill's name,
# whether it loads, its messages) and `load_template_from_file` (the
# template's description) run as bend/skill_load.bend `check` and
# `summary` through the entry bend/ffi_skill_load.bend. The spellers and
# the reader below are its wire grammar written with the wire primitives
# alone (laws/wire.bend proves their round trips); they never call the
# entry's own codec. Lengths are UTF-8 bytes (Rust's `str::len`); blank
# and trim are over Rust's `char::is_whitespace`.

# Terms
# -----

# Unicode White_Space: 9-13, 32, 133, 160, 5760, 8192-8202, 8232, 8233,
# 8239, 8287, 12288
def ws_spec(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.and(U32.is_le(9, x), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 133), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_le(8192, x), U32.is_le(x, 8202)), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), U32.is_eq(x, 12288)))))))))))

# every char is whitespace
def blank_spec(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(ws_spec(c), blank_spec(t))

def utf8_spec.code(one: Bool, two: Bool, three: Bool) -> Nat:
  match one:
    case True{}:
      1n
    case False{}:
      match two:
        case True{}:
          2n
        case False{}:
          match three:
            case True{}:
              3n
            case False{}:
              4n

# a char's UTF-8 length: 1 below 0x80, 2 below 0x800, 3 below 0x10000, 4
def utf8_spec(c: Char) -> Nat:
  match c:
    case Chr{+x}:
      utf8_spec.code(U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536))

# n plus the UTF-8 length of s
def bytes_spec(s: String, n: Nat) -> Nat:
  match s:
    case SNil{}:
      n
    case SCon{c, t}:
      bytes_spec(t, Nat.add(utf8_spec(c), n))

# every char is a-z, 0-9 or '-'
def name_ok(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      match c:
        case Chr{+x}:
          Bool.and(Bool.or(Bool.and(U32.is_le(97, x), U32.is_le(x, 122)), Bool.or(Bool.and(U32.is_le(48, x), U32.is_le(x, 57)), U32.is_eq(x, 45))), name_ok(t))

def msg_if(b: Bool, x: String, xs: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      x <> xs
    case False{}:
      xs

def desc_msgs.go(empty: Bool, +n: Nat) -> List<&2, String>:
  match empty:
    case True{}:
      ["description is required"]
    case False{}:
      msg_if(Nat.is_lt(1024n, n), String.concat(["description exceeds 1024 characters (", Nat.show(n), ")"]), [])

# a blank description is required; past 1024 bytes it is too long
def desc_msgs(+d: String) -> List<&2, String>:
  desc_msgs.go(blank_spec(d), bytes_spec(d, 0n))

# the name's messages, in order: not its dir's name, past 64 bytes, a char
# but a-z 0-9 '-' (or empty), a hyphen at an end, two hyphens in a row
def name_msgs(+name: String, +parent: String) -> List<&2, String>:
  +n = bytes_spec(name, 0n)
  msg_if(Bool.not(String.eq(name, parent)), String.concat(["name \"", name, "\" does not match parent directory \"", parent, "\""]), msg_if(Nat.is_lt(64n, n), String.concat(["name exceeds 64 characters (", Nat.show(n), ")"]), msg_if(Bool.or(Bool.not(name_ok(name)), String.is_empty(name)), "name contains invalid characters (must be lowercase a-z, 0-9, hyphens only)", msg_if(Bool.or(String.starts_with(name, "-"), String.ends_with(name, "-")), "name must not start or end with a hyphen", msg_if(String.contains(name, "--"), "name must not contain consecutive hyphens", [])))))

def or_empty(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      ""
    case Some{d}:
      d

def name_spec.pick(empty: Bool, n: String, parent: String) -> String:
  match empty:
    case True{}:
      parent
    case False{}:
      n

# the frontmatter's name unless missing or empty, else the dir's
def name_spec(m: Maybe<&2, String>, +parent: String) -> String:
  match m:
    case None{}:
      parent
    case Some{+n}:
      name_spec.pick(String.is_empty(n), n, parent)

# whitespace dropped at the start: c then t, where space says c is one
def trim_spec.go(t: String, space: Bool, c: Char) -> String:
  match t:
    case SNil{}:
      match space:
        case True{}:
          SNil{}
        case False{}:
          SCon{c, SNil{}}
    case SCon{+d, r}:
      match space:
        case True{}:
          trim_spec.go(r, ws_spec(d), d)
        case False{}:
          SCon{c, SCon{d, r}}

def trim_spec.start(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      trim_spec.go(t, ws_spec(c), c)

# whitespace dropped at both ends
def trim_spec(s: String) -> String:
  String.reverse(trim_spec.start(String.reverse(trim_spec.start(s))))

def first_spec.go(ls: List<&2, String>, empty: Bool, l: String) -> String:
  match ls:
    case Nil{}:
      match empty:
        case True{}:
          ""
        case False{}:
          trim_spec(l)
    case +m <> rest:
      match empty:
        case True{}:
          first_spec.go(rest, blank_spec(m), m)
        case False{}:
          trim_spec(l)

# the first line that is not blank, trimmed ("" when none)
def first_spec(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case +l <> rest:
      first_spec.go(rest, blank_spec(l), l)

def cut_spec.if(long: Bool, l: String) -> String:
  match long:
    case True{}:
      String.concat([String.take(l, 60n), "..."])
    case False{}:
      l

# more than 60 chars: the first 60, then "..."
def cut_spec(+l: String) -> String:
  cut_spec.if(Nat.is_lt(60n, String.length(l)), l)

def summary_spec.pick(empty: Bool, d: String, body: String) -> String:
  match empty:
    case True{}:
      cut_spec(first_spec(String.lines(body)))
    case False{}:
      d

def summary_spec.go(+d: String, body: String) -> String:
  summary_spec.pick(String.is_empty(d), d, body)

# a template's description: the frontmatter's unless missing or empty,
# else its body's first line that is not blank, trimmed and cut
def summary_spec(m: Maybe<&2, String>, body: String) -> String:
  summary_spec.go(or_empty(m), body)

# Spellers

def spell_text(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))

# the request Rust writes for a
def spell_ask(a: Sk.Ask) -> String:
  match a:
    case Sk.AskSkill{n, p, d}:
      Wr.put_nat(0n, spell_text(n, Wr.put_str(p, spell_text(d, ""))))
    case Sk.AskTemplate{d, b}:
      Wr.put_nat(1n, spell_text(d, Wr.put_str(b, "")))

def text_fits(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      LawsBase.wire_fits(String.length(x))

# every string of a fits the wire
def ask_fits(a: Sk.Ask) -> Bool:
  match a:
    case Sk.AskSkill{n, p, d}:
      Bool.and(text_fits(n), Bool.and(LawsBase.wire_fits(String.length(p)), text_fits(d)))
    case Sk.AskTemplate{d, b}:
      Bool.and(text_fits(d), LawsBase.wire_fits(String.length(b)))

def spell_strs(xs: List<&2, String>, rest: String) -> String:
  match xs:
    case Nil{}:
      rest
    case x <> t:
      Wr.put_str(x, spell_strs(t, rest))

def spell_skill(+name: String, +parent: String, +d: String) -> String:
  +ms = List.append(&2, String, desc_msgs(d), name_msgs(name, parent))
  Wr.put_bool(Bool.not(blank_spec(d)), Wr.put_str(name, Wr.put_nat(List.length(&2, String, ms), spell_strs(ms, ""))))

# the reply to a: a skill loads unless its description is blank, then its
# name, then its messages (the description's first); a template's
# description
def spell_answer(a: Sk.Ask) -> String:
  match a:
    case Sk.AskSkill{n, +p, d}:
      spell_skill(name_spec(n, p), p, or_empty(d))
    case Sk.AskTemplate{d, b}:
      Wr.put_str(summary_spec(d, b), "")

# Reader: the requests the entry accepts, read with the wire primitives

def read_text.some(r: Wr.Dec<String>) -> Wr.Dec<Maybe<&2, String>>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Some{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_text.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, String>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      read_text.some(Wr.get_str(s))
    case 2n+p:
      Wr.Bad{}

def read_text.go(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, String>>:
  match r:
    case Wr.Got{t, s}:
      read_text.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_text(s: String) -> Wr.Dec<Maybe<&2, String>>:
  read_text.go(Wr.get_nat(s))

def read_skill.desc(n: Maybe<&2, String>, p: String, r: Wr.Dec<Maybe<&2, String>>) -> Wr.Dec<Sk.Ask>:
  match r:
    case Wr.Got{d, s}:
      Wr.Got{Sk.AskSkill{n, p, d}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_skill.parent(n: Maybe<&2, String>, r: Wr.Dec<String>) -> Wr.Dec<Sk.Ask>:
  match r:
    case Wr.Got{p, s}:
      read_skill.desc(n, p, read_text(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_skill(r: Wr.Dec<Maybe<&2, String>>) -> Wr.Dec<Sk.Ask>:
  match r:
    case Wr.Got{n, s}:
      read_skill.parent(n, Wr.get_str(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_template.body(d: Maybe<&2, String>, r: Wr.Dec<String>) -> Wr.Dec<Sk.Ask>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{Sk.AskTemplate{d, b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read_template(r: Wr.Dec<Maybe<&2, String>>) -> Wr.Dec<Sk.Ask>:
  match r:
    case Wr.Got{d, s}:
      read_template.body(d, Wr.get_str(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.tag(t: Nat, s: String) -> Wr.Dec<Sk.Ask>:
  match t:
    case 0n:
      read_skill(read_text(s))
    case 1n:
      read_template(read_text(s))
    case 2n+p:
      Wr.Bad{}

def read_ask.go(r: Wr.Dec<Nat>) -> Wr.Dec<Sk.Ask>:
  match r:
    case Wr.Got{t, s}:
      read_ask.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read_ask.end(whole: Bool, a: Sk.Ask) -> Maybe<&2, Sk.Ask>:
  match whole:
    case True{}:
      Some{a}
    case False{}:
      None{}

def read_ask.whole(r: Wr.Dec<Sk.Ask>) -> Maybe<&2, Sk.Ask>:
  match r:
    case Wr.Got{a, s}:
      read_ask.end(Wr.end(s), a)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def read_ask(s: String) -> Maybe<&2, Sk.Ask>:
  read_ask.whole(read_ask.go(Wr.get_nat(s)))

# Laws
# ----

# LAW skill_ffi_answers: on every request Rust writes, the entry answers: a skill file loads unless its description is blank (all Unicode whitespace); its name is the frontmatter's unless missing or empty, else its dir's; its messages are, in order, "description is required" for a blank description or "description exceeds 1024 characters (N)" past 1024 bytes, then the name's: not its dir's name, past 64 bytes, a char but a-z 0-9 '-' or empty, a hyphen at an end, two hyphens in a row; a template's description is the frontmatter's unless missing or empty, else its body's first non-blank line, trimmed, cut to 60 chars and "..." when longer
law skill_ffi_answers:
  for +a: Sk.Ask
  for fits: {ask_fits(a) == True{} : Bool}
  {FSk.ffi(spell_ask(a)) == spell_answer(a) : String}

# LAW skill_ffi_malformed: every input that is not exactly one request gets the error form
law skill_ffi_malformed:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, Sk.Ask>}
  {LawsBase.wire_opens_err(FSk.ffi(s)) == True{} : Bool}

# LAW skill_ffi_example: anchor: the strings Rust sends: a good skill; a skill with no name and an ideographic-space description in a dir "Bad--"; a template with no description; a template with an empty description and a long first line; input left over is refused
law skill_ffi_example:
  {FSk.ffi("0,1,10,web-search10,web-search1,14,Search the web") == "T10,web-search0," : String} &
  {FSk.ffi("0,0,5,Bad--1,2,\u{3000} ") == "F5,Bad--4,23,description is required75,name contains invalid characters (must be lowercase a-z, 0-9, hyphens only)40,name must not start or end with a hyphen41,name must not contain consecutive hyphens" : String} &
  {FSk.ffi("1,0,8,\n  hi \nx") == "2,hi" : String} &
  {FSk.ffi("1,1,0,64,  01234567890123456789012345678901234567890123456789012345678901") == "63,012345678901234567890123456789012345678901234567890123456789..." : String} &
  {read_ask("1,1,5,given1,xy") == None{} : Maybe<&2, Sk.Ask>} &
  {LawsBase.wire_opens_err(FSk.ffi("1,1,5,given1,xy")) == True{} : Bool}

# LAW skill_ffi_malformed_exact: every input that is not exactly one request gets exactly the error form 'E ', then "skill_load: malformed request" (the text Rust's Reader reports)
law skill_ffi_malformed_exact:
  for +s: String
  for no: {read_ask(s) == None{} : Maybe<&2, Sk.Ask>}
  {FSk.ffi(s) == SCon{'E', SCon{' ', "skill_load: malformed request"}} : String}
