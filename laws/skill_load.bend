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
# path and error. crates/eukhe-core/src/skills: `load_skill_from_file`
# (the skill's name, whether it loads, its messages) and
# `load_template_from_file` (the template's description) run as
# bend/skill_load.bend `check` and `summary` through the entry
# bend/ffi_skill_load.bend. The checks are the Agent Skills limits Rust
# documents (crates/eukhe-core/src/skills/check.rs, its test vectors).
# Lengths in bytes are UTF-8 bytes (Rust `str::len`, sl_bytes);
# whitespace is Unicode White_Space (Rust `char::is_whitespace`: the table
# sl_white). Every input is free.
#
# L5 splits into:
# R1: the path of every candidate file is on the loaded list or named by
#     a diagnostic.
# R2: of candidates with distinct paths, no path is both loaded and named.
# R3: the loaded list is the paths of the candidates that read well, in
#     the candidates' order.
# R4: the diagnostics are one per candidate that does not load, in the
#     candidates' order, naming its path and its kind: 0 unreadable, 1
#     malformed frontmatter, 2 no description.
# R5: a skill file loads exactly when its description (a missing one is
#     empty) holds a char that is not White_Space.
# R6: a skill's messages open with its description's: "description is
#     required" for a blank one; else "description exceeds 1024 characters
#     (N)" when it has N > 1024 bytes; else none.
# R7: a skill's name is its frontmatter's, unless missing or empty; then
#     its dir's.
# R8: then come its name's messages, each exactly when its rule holds, in
#     this order: (a) `name "N" does not match parent directory "P"` when
#     the name is not the dir's; (b) "name exceeds 64 characters (K)" when
#     it has K > 64 bytes; (c) "name contains invalid characters (must be
#     lowercase a-z, 0-9, hyphens only)" when it is empty or holds a char
#     other than a-z, 0-9, '-'; (d) "name must not start or end with a
#     hyphen" when its first or last char is '-'; (e) "name must not
#     contain consecutive hyphens" when a '-' follows a '-'.
# R9: a template's description is its frontmatter's unless missing or
#     empty; else its body's first line that is not blank, trimmed of
#     White_Space at both ends ("" when every line is blank), and when that
#     has more than 60 chars, its first 60 chars and "...".
# R10: the entry answers each request Rust writes (every length within the
#     wire) with the spelled check (T|F it loads, the name, the count of
#     messages and each) or the spelled description, and answers every
#     other input with the exact error form `E skill_load: malformed
#     request` (the text Rust's Reader reports).

# The loader: R1-R4
# -----------------

# LAW skill_failure_reported (R1): for every list of candidates and every
# index into it, the path of the candidate there is on the loaded list or
# named by a diagnostic
# EXCLUDES: a candidate dropped without a word, at any position
law skill_failure_reported:
  for cs: List<&2, Sk.Cand>
  for i: Nat
  for +c: Sk.Cand
  for at: {List.get(&2, Sk.Cand, cs, i) == Some{c} : Maybe<&2, Sk.Cand>}
  {Bool.or(Sk.listed(Sk.loaded(cs), Sk.Cand.path(c)), Sk.listed(Sk.named(Sk.diags(cs)), Sk.Cand.path(c))) == True{} : Bool}

# LAW skill_loaded_not_failed (R2): of distinct candidates, no file both loads and fails
law skill_loaded_not_failed:
  for cs: List<&2, Sk.Cand>
  for +n: Nat
  for +d: {Sk.distinct(cs) == True{} : Bool}
  {Bool.and(Sk.listed(Sk.loaded(cs), n), Sk.listed(Sk.named(Sk.diags(cs)), n)) == False{} : Bool}

# LAW skill_distinct_example: witness: candidates of two paths are distinct, two of one path are not (so skill_loaded_not_failed is not vacuous)
law skill_distinct_example:
  {Sk.distinct([Sk.Cand{0n, Sk.Good{}}, Sk.Cand{1n, Sk.Unreadable{}}]) == True{} : Bool} &
  {Sk.distinct([Sk.Cand{0n, Sk.Good{}}, Sk.Cand{0n, Sk.Malformed{}}]) == False{} : Bool}

# LAW skill_loaded_order (R3): the loaded list of the candidates xs then ys
# is the loaded list of xs, then that of ys, for every xs and ys
# EXCLUDES: loaded paths reordered (sorted, reversed), moved across
#   candidates, duplicated or dropped by a neighbour
law skill_loaded_order:
  for +xs: List<&2, Sk.Cand>
  for +ys: List<&2, Sk.Cand>
  {Sk.loaded(List.append(&2, Sk.Cand, xs, ys)) == List.append(&2, Nat, Sk.loaded(xs), Sk.loaded(ys)) : List<&2, Nat>}

# LAW skill_loaded_one (R3): one candidate of path p loads p when it reads
# well and nothing when it is unreadable, malformed or incomplete (with
# skill_loaded_order this fixes the loaded list of every list)
# EXCLUDES: a failed file loaded, a good file not loaded, another path
law skill_loaded_one:
  for +p: Nat
  {Sk.loaded([Sk.Cand{p, Sk.Good{}}]) == [p] : List<&2, Nat>} &
  {Sk.loaded([Sk.Cand{p, Sk.Unreadable{}}]) == [] : List<&2, Nat>} &
  {Sk.loaded([Sk.Cand{p, Sk.Malformed{}}]) == [] : List<&2, Nat>} &
  {Sk.loaded([Sk.Cand{p, Sk.Incomplete{}}]) == [] : List<&2, Nat>}

# LAW skill_diags_order (R4): the diagnostics of the candidates xs then ys
# are those of xs, then those of ys, for every xs and ys
# EXCLUDES: diagnostics reordered, merged, duplicated or dropped
law skill_diags_order:
  for +xs: List<&2, Sk.Cand>
  for +ys: List<&2, Sk.Cand>
  {Sk.diags(List.append(&2, Sk.Cand, xs, ys)) == List.append(&2, Sk.Diag, Sk.diags(xs), Sk.diags(ys)) : List<&2, Sk.Diag>}

# LAW skill_diags_one (R4): one candidate of path p gets no diagnostic when
# it reads well, else one naming p with kind 0 unreadable, 1 malformed, 2
# no description (with skill_diags_order this fixes the diagnostics of
# every list)
# EXCLUDES: a kind swapped, a diagnostic for a good file, another path
law skill_diags_one:
  for +p: Nat
  {Sk.diags([Sk.Cand{p, Sk.Good{}}]) == [] : List<&2, Sk.Diag>} &
  {Sk.diags([Sk.Cand{p, Sk.Unreadable{}}]) == [Sk.Diag{p, 0n}] : List<&2, Sk.Diag>} &
  {Sk.diags([Sk.Cand{p, Sk.Malformed{}}]) == [Sk.Diag{p, 1n}] : List<&2, Sk.Diag>} &
  {Sk.diags([Sk.Cand{p, Sk.Incomplete{}}]) == [Sk.Diag{p, 2n}] : List<&2, Sk.Diag>}

# The checks of a skill file and a template: R5-R9
# ------------------------------------------------

# Terms

def sl_utf8.pick(b: Bool, x: Nat, y: Nat) -> Nat:
  match b:
    case True{}:
      x
    case False{}:
      y

# R6, R8 (and laws/slash_suggest.bend R3): the bytes of a char's UTF-8
# encoding (RFC 3629 section 3): 1 below U+0080, 2 below U+0800, 3 below
# U+10000, else 4
def sl_utf8(c: Char) -> Nat:
  match c:
    case Chr{+x}:
      sl_utf8.pick(U32.is_lt(x, 128), 1n, sl_utf8.pick(U32.is_lt(x, 2048), 2n, sl_utf8.pick(U32.is_lt(x, 65536), 3n, 4n)))

# the bytes of a text's UTF-8 encoding (Rust `str::len`): the sum over its
# chars
def sl_bytes(s: String) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{c, t}:
      Nat.add(sl_utf8(c), sl_bytes(t))

# x lies in lo..hi
def sl_in(+x: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_le(lo, x), U32.is_le(x, hi))

# R5-R9: a White_Space char (Unicode PropList.txt White_Space, the set Rust's
# `char::is_whitespace` holds for): U+0009-U+000D, U+0020, U+0085, U+00A0,
# U+1680, U+2000-U+200A, U+2028, U+2029, U+202F, U+205F, U+3000
def sl_white(c: Char) -> Bool:
  +x = Char.to_u32(c)
  Bool.or(sl_in(x, 9, 13), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 133), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(sl_in(x, 8192, 8202), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), U32.is_eq(x, 12288)))))))))))

# R5, R6, R9: every char is White_Space (the empty text too)
def sl_blank(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(sl_white(c), sl_blank(t))

# R5, R6: the description's text; a missing one is empty
def sl_desc(m: Maybe<&2, String>) -> String:
  match m:
    case None{}:
      ""
    case Some{d}:
      d

# R8c: a char a name may hold: a-z, 0-9, '-'
def sl_name_char(c: Char) -> Bool:
  +x = Char.to_u32(c)
  Bool.or(sl_in(x, 97, 122), Bool.or(sl_in(x, 48, 57), U32.is_eq(x, 45)))

def sl_name_chars(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(sl_name_char(c), sl_name_chars(t))

# R8c: a name that is not empty and holds only a-z, 0-9, '-'
def sl_name_ok(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Bool.and(sl_name_char(c), sl_name_chars(t))

# R8d: the first char of s is '-'
def sl_dash_first(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{c, t}:
      Char.is_eq(c, '-')

# R8d: the first or the last char of s is '-'
def sl_edge(+s: String) -> Bool:
  Bool.or(sl_dash_first(s), sl_dash_first(String.reverse(s)))

# R8e: a '-' follows a '-' in s, where prev says the char before s is '-'
def sl_pair.go(s: String, prev: Bool) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, t}:
      +d = Char.is_eq(c, '-')
      Bool.or(Bool.and(prev, d), sl_pair.go(t, d))

# R8e: a '-' follows a '-' in s
def sl_pair(s: String) -> Bool:
  sl_pair.go(s, False{})

# x alone when b, else nothing
def sl_only(b: Bool, x: String) -> List<&2, String>:
  match b:
    case True{}:
      [x]
    case False{}:
      []

# R6, R8: the messages of a skill named name, in a dir named parent, with
# the description d, in their order
def sl_messages(+name: String, +parent: String, +d: String) -> List<&2, String>:
  +n = sl_bytes(d)
  +k = sl_bytes(name)
  +blank = sl_blank(d)
  List.concat(&2, String, [sl_only(blank, "description is required"), sl_only(Bool.and(Bool.not(blank), Nat.is_lt(1024n, n)), String.concat(["description exceeds 1024 characters (", Nat.show(n), ")"])), sl_only(Bool.not(String.eq(name, parent)), String.concat(["name \"", name, "\" does not match parent directory \"", parent, "\""])), sl_only(Nat.is_lt(64n, k), String.concat(["name exceeds 64 characters (", Nat.show(k), ")"])), sl_only(Bool.not(sl_name_ok(name)), "name contains invalid characters (must be lowercase a-z, 0-9, hyphens only)"), sl_only(sl_edge(name), "name must not start or end with a hyphen"), sl_only(sl_pair(name), "name must not contain consecutive hyphens")])

# the parts of a check
def sl_loaded(c: Sk.Checked) -> Bool:
  match c:
    case Sk.Checked{l, n, ms}:
      l

def sl_name(c: Sk.Checked) -> String:
  match c:
    case Sk.Checked{l, n, ms}:
      n

def sl_msgs(c: Sk.Checked) -> List<&2, String>:
  match c:
    case Sk.Checked{l, n, ms}:
      ms

# R9: s without its White_Space chars at the start
def sl_drop_start.at(w: Bool, c: Char, t: String, r: String) -> String:
  match w:
    case True{}:
      r
    case False{}:
      SCon{c, t}

def sl_drop_start(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      sl_drop_start.at(sl_white(c), c, t, sl_drop_start(t))

# R9: s without its White_Space chars at the end: c then r, where r is the
# rest so dropped and w says c is White_Space
def sl_drop_end.at(w: Bool, c: Char, r: String) -> String:
  match w:
    case True{}:
      match r:
        case SNil{}:
          SNil{}
        case SCon{d, u}:
          SCon{c, SCon{d, u}}
    case False{}:
      SCon{c, r}

def sl_drop_end(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      sl_drop_end.at(sl_white(c), c, sl_drop_end(t))

# R9: s without White_Space at both ends
def sl_trim(s: String) -> String:
  sl_drop_end(sl_drop_start(s))

# R9: a line that is not blank
def sl_dark(l: String) -> Bool:
  Bool.not(sl_blank(l))

def sl_head(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      l

# R9: the first line of ls that is not blank, trimmed ("" when none)
def sl_line(ls: List<&2, String>) -> String:
  sl_trim(sl_head(List.filter(~String, ~sl_dark, ls)))

# Laws

# LAW skill_loads_iff_described (R5): for every frontmatter name, dir and
# description, the skill file loads exactly when its description (a
# missing one is empty) holds a char that is not White_Space
# EXCLUDES: a blank (spaces, NBSP, ideographic space) description loaded,
#   ASCII-only whitespace, a missing description loaded, a real one refused
law skill_loads_iff_described:
  for m: Maybe<&2, String>
  for +parent: String
  for +dm: Maybe<&2, String>
  {sl_loaded(Sk.check(m, parent, dm)) == Bool.not(sl_blank(sl_desc(dm))) : Bool}

# LAW skill_name_falls_back (R7): for every dir and description, a skill's
# name is its dir's when the frontmatter's is missing or empty, and the
# frontmatter's when it has a char
# EXCLUDES: an empty name kept, the dir's name over a given one
law skill_name_falls_back:
  for +parent: String
  for +dm: Maybe<&2, String>
  for +c: Char
  for +t: String
  {sl_name(Sk.check(None{}, parent, dm)) == parent : String} &
  {sl_name(Sk.check(Some{""}, parent, dm)) == parent : String} &
  {sl_name(Sk.check(Some{SCon{c, t}}, parent, dm)) == SCon{c, t} : String}

# LAW skill_messages (R6, R8): for every frontmatter name, dir and
# description, a skill's messages are the description's (R6), then its
# name's (R8 a-e, of the name the check reports), each exactly when its
# rule holds, in that order
# EXCLUDES: a message missing or added, two in another order, a count in
#   chars not UTF-8 bytes, a limit off by one, an empty name passed, a
#   hyphen rule read on the wrong end, the too-long message beside the
#   required one, a text changed
law skill_messages:
  for +m: Maybe<&2, String>
  for +parent: String
  for +dm: Maybe<&2, String>
  {sl_msgs(Sk.check(m, parent, dm)) == sl_messages(sl_name(Sk.check(m, parent, dm)), parent, sl_desc(dm)) : List<&2, String>}

# LAW skill_template_given (R9): for every body, a template whose
# frontmatter has a description with a char gets that description
# EXCLUDES: a given description trimmed, cut or replaced by the body's
law skill_template_given:
  for +d: String
  for e: {String.is_empty(d) == False{} : Bool}
  for body: String
  {Sk.summary(Some{d}, body) == d : String}

# LAW skill_template_short (R9): with no description (missing or empty),
# a template's description is its body's first line that is not blank,
# trimmed ("" when every line is blank), when that has at most 60 chars
# EXCLUDES: a blank line taken, a later line taken, a line left untrimmed
#   or trimmed of ASCII spaces only, a short line cut
law skill_template_short:
  for +body: String
  for +s: {Nat.is_lt(60n, String.length(sl_line(String.lines(body)))) == False{} : Bool}
  {Sk.summary(None{}, body) == sl_line(String.lines(body)) : String} &
  {Sk.summary(Some{""}, body) == sl_line(String.lines(body)) : String}

# LAW skill_template_long (R9): with no description (missing or empty),
# when that line has more than 60 chars, the description is its first 60
# chars, then "..."
# EXCLUDES: a long line kept whole, cut at 60 bytes or after another count,
#   the "..." lost
law skill_template_long:
  for +body: String
  for +s: {Nat.is_lt(60n, String.length(sl_line(String.lines(body)))) == True{} : Bool}
  {Sk.summary(None{}, body) == String.append(String.take(sl_line(String.lines(body)), 60n), "...") : String} &
  {Sk.summary(Some{""}, body) == String.append(String.take(sl_line(String.lines(body)), 60n), "...") : String}

# The entry: R10
# --------------

# a string that may be missing, then rest (WIRE.md: 0 none | 1 and the
# string)
def spell_text(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))

# the request Rust writes for a, then rest: tag 0 a skill (its name, its
# dir's name, its description), tag 1 a template (its description, its
# body)
def spell_ask(a: Sk.Ask, rest: String) -> String:
  match a:
    case Sk.AskSkill{n, p, d}:
      Wr.put_nat(0n, spell_text(n, Wr.put_str(p, spell_text(d, rest))))
    case Sk.AskTemplate{d, b}:
      Wr.put_nat(1n, spell_text(d, Wr.put_str(b, rest)))

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

# the reply of a check: T|F it loads, its name, the count of its messages
# and each
def spell_checked(c: Sk.Checked) -> String:
  match c:
    case Sk.Checked{l, n, ms}:
      Wr.put_bool(l, Wr.put_str(n, LawsBase.wire_spell_strs(ms, "")))

# the reply to a: the spelled check of the skill, or the spelled
# description of the template (both pinned by R5-R9's laws)
def spell_reply(a: Sk.Ask) -> String:
  match a:
    case Sk.AskSkill{n, p, d}:
      spell_checked(Sk.check(n, p, d))
    case Sk.AskTemplate{d, b}:
      Wr.put_str(Sk.summary(d, b), "")

# LAW skill_ffi_answers (R10): on every request Rust writes (every string
# within the wire), the entry answers the spelled check of the skill
# (Sk.check: whether it loads, its name, its messages) or the spelled
# description of the template (Sk.summary)
# EXCLUDES: fields read in another order or from the wrong tag, a missing
#   string read as empty, a reply spelled in another grammar, a default
law skill_ffi_answers:
  for +a: Sk.Ask
  for fits: {ask_fits(a) == True{} : Bool}
  {FSk.ffi(spell_ask(a, "")) == spell_reply(a) : String}

# LAW skill_ffi_only_requests (R10): every input the entry does not answer
# with the error form is a spelled request whose strings fit the wire,
# with nothing after it
# EXCLUDES: an answer to input left over after a request, an unknown tag,
#   a malformed field or a missing-string tag other than 0 and 1 read as a
#   request
law skill_ffi_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FSk.ffi(s)) == False{} : Bool}
  exs a: Sk.Ask
  {s == spell_ask(a, "") : String} & {ask_fits(a) == True{} : Bool}

# LAW skill_ffi_refuses (R10): every error the entry answers is exactly
# `E skill_load: malformed request`
# EXCLUDES: an error text that varies with the input, a second error form
law skill_ffi_refuses:
  for +s: String
  for bad: {LawsBase.wire_opens_err(FSk.ffi(s)) == True{} : Bool}
  {FSk.ffi(s) == Wr.err("skill_load: malformed request") : String}

# LAW skill_ffi_example (R5-R10): anchor: the strings Rust sends: a good
# skill; a skill with no name and an ideographic-space description in a
# dir "Bad--"; Rust's own test vector (crates/eukhe-core/src/skills/
# check.rs: a name of 32 'é' and '-' in dir "dir", 65 bytes); a template
# with no description; a template with an empty description and a long
# first line; input left over and an unknown tag refused
law skill_ffi_example:
  {FSk.ffi("0,1,10,web-search10,web-search1,14,Search the web") == "T10,web-search0," : String} &
  {FSk.ffi("0,0,5,Bad--1,2,\u{3000} ") == "F5,Bad--4,23,description is required75,name contains invalid characters (must be lowercase a-z, 0-9, hyphens only)40,name must not start or end with a hyphen41,name must not contain consecutive hyphens" : String} &
  {Sk.check(Some{"éééééééééééééééééééééééééééééééé-"}, "dir", Some{"d"}) == Sk.Checked{True{}, "éééééééééééééééééééééééééééééééé-", ["name \"éééééééééééééééééééééééééééééééé-\" does not match parent directory \"dir\"", "name exceeds 64 characters (65)", "name contains invalid characters (must be lowercase a-z, 0-9, hyphens only)", "name must not start or end with a hyphen"]} : Sk.Checked} &
  {FSk.ffi("1,0,8,\n  hi \nx") == "2,hi" : String} &
  {FSk.ffi("1,1,0,64,  01234567890123456789012345678901234567890123456789012345678901") == "63,012345678901234567890123456789012345678901234567890123456789..." : String} &
  {FSk.ffi("1,1,5,given1,xy") == Wr.err("skill_load: malformed request") : String} &
  {FSk.ffi("2,") == Wr.err("skill_load: malformed request") : String}
