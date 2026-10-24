# skill_load: what the skill and prompt template loaders do with each
# candidate file. The Rust code is crates/eukhe-core/src/skills/
# (`load_skills_from_dir` and `load_skill_from_file` in discovery.rs,
# `load_prompt_templates` in prompt_templates.rs). The checks of a skill
# file's frontmatter (`check`) and a template's description (`summary`)
# run as this code (entry bend/ffi_skill_load.bend); Rust reads the files
# and parses the YAML.
#
# A candidate is a file the loader found (a SKILL.md, a root `.md` skill,
# a template `.md`), with its path and how reading it ends:
#
#   - good: the file loads; its path joins the loaded list;
#   - unreadable: the file or its metadata is not read (a read error,
#     text that is not UTF-8, a dangling link): a diagnostic with its
#     path, kind 0;
#   - malformed: its frontmatter is not valid YAML: a diagnostic with its
#     path, kind 1;
#   - incomplete: a skill without a description: a diagnostic with its
#     path, kind 2.
#
# No candidate is dropped without a word.

import Base

type Outcome is Data:
  Good{}
  Unreadable{}
  Malformed{}
  Incomplete{}

# One candidate file: its path and how reading it ends.
type Cand is Data:
  Cand{path: Nat, o: Outcome}

# One diagnostic: the path it names and its kind.
type Diag is Data:
  Diag{path: Nat, kind: Nat}

def Cand.path(c: Cand) -> Nat:
  match c:
    case Cand{p, o}:
      p

def Diag.path(d: Diag) -> Nat:
  match d:
    case Diag{p, k}:
      p

# c is in cs
def In(+c: Cand, cs: List<&2, Cand>) -> Type:
  match cs:
    case Nil{}:
      Empty
    case +x <> rest:
      Or({c == x : Cand}, In(c, rest))

# The loader
# ----------

# the paths of the candidates that load
def loaded(cs: List<&2, Cand>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      match c:
        case Cand{p, o}:
          match o:
            case Good{}:
              p <> loaded(rest)
            case Unreadable{}:
              loaded(rest)
            case Malformed{}:
              loaded(rest)
            case Incomplete{}:
              loaded(rest)

# the diagnostics of the candidates that do not load
def diags(cs: List<&2, Cand>) -> List<&2, Diag>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      match c:
        case Cand{p, o}:
          match o:
            case Good{}:
              diags(rest)
            case Unreadable{}:
              Diag{p, 0n} <> diags(rest)
            case Malformed{}:
              Diag{p, 1n} <> diags(rest)
            case Incomplete{}:
              Diag{p, 2n} <> diags(rest)

# The lists
# ---------

# the paths the diagnostics ds name
def named(ds: List<&2, Diag>) -> List<&2, Nat>:
  match ds:
    case Nil{}:
      Nil{}
    case d <> rest:
      Diag.path(d) <> named(rest)

# the paths of the candidates cs
def paths(cs: List<&2, Cand>) -> List<&2, Nat>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      Cand.path(c) <> paths(rest)

# n is in ns
def listed(ns: List<&2, Nat>, +n: Nat) -> Bool:
  match ns:
    case Nil{}:
      False{}
    case x <> rest:
      Bool.or(Nat.is_eq(x, n), listed(rest, n))

# no two candidates of cs share a path
def distinct(cs: List<&2, Cand>) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case +c <> +rest:
      Bool.and(Bool.not(listed(paths(rest), Cand.path(c))), distinct(rest))

# The checks Rust asks for
# ------------------------

# a char Rust's `char::is_whitespace` holds for (Unicode White_Space)
def ws.code(+x: U32) -> Bool:
  Bool.or(Bool.and(U32.is_le(9, x), U32.is_le(x, 13)), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 133), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(Bool.and(U32.is_le(8192, x), U32.is_le(x, 8202)), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), U32.is_eq(x, 12288)))))))))))

def ws(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      ws.code(x)

# every char of s is whitespace (Rust: `s.trim().is_empty()`)
def blank(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(ws(c), blank(t))

def utf8.code(one: Bool, two: Bool, three: Bool) -> Nat:
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

# the UTF-8 length of a char
def utf8(c: Char) -> Nat:
  match c:
    case Chr{+x}:
      utf8.code(U32.is_lt(x, 128), U32.is_lt(x, 2048), U32.is_lt(x, 65536))

# n plus the UTF-8 length of s (Rust: `s.len()`), one flat loop
def bytes(s: String, n: Nat) -> Nat:
  match s:
    case SNil{}:
      n
    case SCon{c, t}:
      bytes(t, Nat.add(utf8(c), n))

# a char a skill name may hold: a-z, 0-9, '-'
def name.char(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(Bool.and(U32.is_le(97, x), U32.is_le(x, 122)), Bool.or(Bool.and(U32.is_le(48, x), U32.is_le(x, 57)), U32.is_eq(x, 45)))

def name.chars(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(name.char(c), name.chars(t))

# the longest name and description, in UTF-8 bytes
def name.max() -> Nat:
  64n

def desc.max() -> Nat:
  1024n

def when(b: Bool, x: String, xs: List<&2, String>) -> List<&2, String>:
  match b:
    case True{}:
      x <> xs
    case False{}:
      xs

def desc.msgs.go(empty: Bool, +n: Nat) -> List<&2, String>:
  match empty:
    case True{}:
      ["description is required"]
    case False{}:
      when(Nat.is_lt(desc.max(), n), String.concat(["description exceeds 1024 characters (", Nat.show(n), ")"]), [])

# the messages of a description: required when blank; too long past
# desc.max() bytes
def desc.msgs(+d: String) -> List<&2, String>:
  desc.msgs.go(blank(d), bytes(d, 0n))

# the messages of a skill's name, in this order: another name than its
# dir's, too long, a char other than a-z 0-9 '-' (or empty), a hyphen at
# either end, two hyphens in a row
def name.msgs(+name: String, +parent: String) -> List<&2, String>:
  +n = bytes(name, 0n)
  when(Bool.not(String.eq(name, parent)), String.concat(["name \"", name, "\" does not match parent directory \"", parent, "\""]), when(Nat.is_lt(name.max(), n), String.concat(["name exceeds 64 characters (", Nat.show(n), ")"]), when(Bool.or(Bool.not(name.chars(name)), String.is_empty(name)), "name contains invalid characters (must be lowercase a-z, 0-9, hyphens only)", when(Bool.or(String.starts_with(name, "-"), String.ends_with(name, "-")), "name must not start or end with a hyphen", when(String.contains(name, "--"), "name must not contain consecutive hyphens", [])))))

def name.pick(empty: Bool, n: String, parent: String) -> String:
  match empty:
    case True{}:
      parent
    case False{}:
      n

# the name of a skill: its frontmatter's, unless missing or empty; then
# its dir's
def name.of(m: Maybe<&2, String>, +parent: String) -> String:
  match m:
    case None{}:
      parent
    case Some{+n}:
      name.pick(String.is_empty(n), n, parent)

def text.of(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      ""
    case Some{d}:
      d

# what the loader makes of a skill file: it loads unless the description
# is blank; its name; every message, the description's first
type Checked is Data:
  Checked{loaded: Bool, name: String, msgs: List<&2, String>}

def check.go(+name: String, +parent: String, +d: String) -> Checked:
  Checked{Bool.not(blank(d)), name, List.append(&2, String, desc.msgs(d), name.msgs(name, parent))}

# the check of a skill file whose frontmatter has name m and description
# dm (each when it is a string), in a dir named parent
def check(m: Maybe<&2, String>, +parent: String, dm: Maybe<&2, String>) -> Checked:
  check.go(name.of(m, parent), parent, text.of(dm))

# trim, as Rust's `str::trim` (Unicode whitespace at both ends)
def trim.go(t: String, space: Bool, c: Char) -> String:
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
          trim.go(r, ws(d), d)
        case False{}:
          SCon{c, SCon{d, r}}

def trim.start(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      trim.go(t, ws(c), c)

def trim(s: String) -> String:
  String.reverse(trim.start(String.reverse(trim.start(s))))

# the first line that is not blank among l, then ls, trimmed (empty: l is
# blank)
def first.go(ls: List<&2, String>, empty: Bool, l: String) -> String:
  match ls:
    case Nil{}:
      match empty:
        case True{}:
          ""
        case False{}:
          trim(l)
    case +m <> rest:
      match empty:
        case True{}:
          first.go(rest, blank(m), m)
        case False{}:
          trim(l)

# the first line of ls that is not blank, trimmed
def first(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case +l <> rest:
      first.go(rest, blank(l), l)

def cut.if(long: Bool, l: String) -> String:
  match long:
    case True{}:
      String.concat([String.take(l, 60n), "..."])
    case False{}:
      l

# a line of more than 60 chars is cut to 60, then "..."
def cut(+l: String) -> String:
  cut.if(Nat.is_lt(60n, String.length(l)), l)

def summary.pick(empty: Bool, d: String, body: String) -> String:
  match empty:
    case True{}:
      cut(first(String.lines(body)))
    case False{}:
      d

def summary.go(+d: String, body: String) -> String:
  summary.pick(String.is_empty(d), d, body)

# a template's description: its frontmatter's (when it is a string and
# not empty); else the first line of its body that is not blank, trimmed
# and cut
def summary(m: Maybe<&2, String>, body: String) -> String:
  summary.go(text.of(m), body)

# what Rust asks: the check of a skill file (its frontmatter's name if it
# is a string, its dir's name, its frontmatter's description if it is a
# string), the description of a template (its frontmatter's if it is a
# string, its body)
type Ask is Data:
  AskSkill{name: Maybe<&2, String>, parent: String, desc: Maybe<&2, String>}
  AskTemplate{desc: Maybe<&2, String>, body: String}
