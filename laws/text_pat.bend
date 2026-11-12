# eukhe: the laws of area text_pat

import Base
import ../bend/text_pat.bend as Tp
import ./base.bend as LawsBase

# (T1) The text patterns of the eukhe-ai error rules
# --------------------------------------------------
# bend/text_pat.bend: the search the overflow and stream-failure rules
# run instead of Rust `regex` patterns (no entry of its own: the entries
# of those rules call it). Every text and every list of items is free.
#
# R1: a char is of a class exactly when: CLit c, it is c; CAny, it is no
#     line feed; CDig, it is an ASCII digit; CDigC, an ASCII digit or a
#     comma; CSp, a Unicode White_Space char (U+0009..U+000D, U+0020,
#     U+0085, U+00A0, U+1680, U+2000..U+200A, U+2028, U+2029, U+202F,
#     U+205F, U+3000: the White_Space lines of Unicode's PropList.txt, the
#     set Rust's regex `\s` takes).
# R2: a text matches a list of items when it splits into one part per
#     item, in order: one char of the class for `One`, any run of chars of
#     the class (the empty run too) for `Star`.
# R3: the prefix test of a text is true exactly when some prefix of the
#     text matches the items; the search is true exactly when some part of
#     the text (a prefix of a suffix) matches them.
# R4: `fold` maps A-Z to a-z, the Kelvin sign U+212A to k and the long s
#     U+017F to s, every other char to itself (Unicode simple case folding,
#     CaseFolding.txt status C and S, as far as it reaches a lowercase
#     ASCII char: a case-insensitive regex matches a lowercase ASCII
#     pattern char exactly where the folded text holds it). `lower` maps
#     A-Z to a-z, U+212A to k, the capital I with dot U+0130 to i then
#     U+0307, every other char to itself (Rust's `to_lowercase`, from
#     UnicodeData.txt's simple lowercase and SpecialCasing.txt's
#     unconditional rows, maps no other char to an ASCII letter, a line
#     feed or more than one char; chars it lowers to a non-ASCII char stay
#     as they are here: an intended difference no lowercase ASCII pattern
#     can see).
# R5: a pattern is found in a text when one of its alternatives is: at
#     the text's start for an anchored pattern (a prefix of the text
#     matches it, R2), in some part of the text for the others; a list of
#     patterns when one of them is.
# Coverage: R1 text_pat_class_table, text_pat_class_lit_self,
# text_pat_class_lit; R2, R3
# text_pat_prefix_sound/complete, text_pat_search_sound/complete; R4
# text_pat_fold, text_pat_lower (tables of the Unicode files); R5
# text_pat_hit_sound/complete, text_pat_any_sound/complete.

# Spec helpers
# ------------

# R1, R4: a row of a Unicode table: one code point, or the code points lo
# to hi (both in)
type SpRow is Data:
  SpOne{c: U32}
  SpRun{lo: U32, hi: U32}

def sp_row_has(+x: U32, w: SpRow) -> Bool:
  match w:
    case SpOne{c}:
      U32.is_eq(x, c)
    case SpRun{lo, hi}:
      Bool.and(U32.is_le(lo, x), U32.is_le(x, hi))

def sp_rows_has.at(t: List<&2, SpRow>, w: SpRow, +x: U32) -> Bool:
  match t:
    case Nil{}:
      sp_row_has(x, w)
    case v <> u:
      Bool.or(sp_row_has(x, w), sp_rows_has.at(u, v, x))

# the code x is in one of the rows ws
def sp_rows_has(+x: U32, ws: List<&2, SpRow>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case w <> t:
      sp_rows_has.at(t, w, x)

# R1: the White_Space code points, one row per line of the White_Space
# entries of Unicode's PropList.txt (Unicode 15.1, unchanged since 6.3):
# 0009..000D, 0020, 0085, 00A0, 1680, 2000..200A, 2028, 2029, 202F, 205F,
# 3000
def sp_white_space() -> List<&2, SpRow>:
  [SpRun{9, 13}, SpOne{32}, SpOne{133}, SpOne{160}, SpOne{5760}, SpRun{8192, 8202}, SpOne{8232}, SpOne{8233}, SpOne{8239}, SpOne{8287}, SpOne{12288}]

# R1: the ASCII digits 0030..0039 (`0` to `9`)
def sp_digits() -> List<&2, SpRow>:
  [SpRun{48, 57}]

# R1: the ASCII digits and the comma 002C
def sp_digits_comma() -> List<&2, SpRow>:
  [SpRun{48, 57}, SpOne{44}]

# R1: the line feed 000A (`.` takes every char but it)
def sp_line_feed() -> List<&2, SpRow>:
  [SpOne{10}]

# R1: the chars of a class: a literal by its code point, the others by
# their table
def sp_cls(k: Tp.Cls, x: Char) -> Bool:
  match k:
    case Tp.CLit{c}:
      U32.is_eq(Char.to_u32(c), Char.to_u32(x))
    case Tp.CAny{}:
      Bool.not(sp_rows_has(Char.to_u32(x), sp_line_feed()))
    case Tp.CDig{}:
      sp_rows_has(Char.to_u32(x), sp_digits())
    case Tp.CDigC{}:
      sp_rows_has(Char.to_u32(x), sp_digits_comma())
    case Tp.CSp{}:
      sp_rows_has(Char.to_u32(x), sp_white_space())

# R2: the text u, whole, matches the items its
def sp_lang(u: String, its: List<&2, Tp.It>) -> Bool:
  match u:
    case SNil{}:
      match its:
        case Nil{}:
          True{}
        case i <> k:
          match i:
            case Tp.One{c}:
              False{}
            case Tp.Star{c}:
              sp_lang(SNil{}, k)
    case SCon{+x, +t}:
      match its:
        case Nil{}:
          False{}
        case i <> +k:
          match i:
            case Tp.One{c}:
              Bool.and(sp_cls(c, x), sp_lang(t, k))
            case Tp.Star{+c}:
              Bool.or(sp_lang(SCon{x, t}, k), Bool.and(sp_cls(c, x), sp_lang(t, Tp.Star{c} <> k)))

# R4: a row of a case table: the code points lo to hi each map to
# themselves plus by (one table line per code point, written as a run),
# or the code point c maps to the chars `to`
type SpCase is Data:
  SpCaseRun{lo: U32, hi: U32, by: U32}
  SpCaseOne{c: U32, to: String}

# R4: the CaseFolding.txt lines of status C or S whose folding is a
# lowercase ASCII letter, in the file's order: 0041..005A (each +0x20),
# 017F -> 0073, 212A -> 006B
def sp_case_folding() -> List<&2, SpCase>:
  [SpCaseRun{65, 90, 32}, SpCaseOne{383, "s"}, SpCaseOne{8490, "k"}]

# R4: the lowercase mappings whose result holds an ASCII letter, in code
# point order: UnicodeData.txt field 13 for 0041..005A (each +0x20) and
# 212A -> 006B; SpecialCasing.txt's unconditional 0130 -> 0069 0307
def sp_lowercase() -> List<&2, SpCase>:
  [SpCaseRun{65, 90, 32}, SpCaseOne{304, SCon{'i', SCon{Chr{775}, SNil{}}}}, SpCaseOne{8490, "k"}]

def sp_case.pick(b: Bool, yes: String, no: String) -> String:
  match b:
    case True{}:
      yes
    case False{}:
      no

# R4: the chars the first row that holds the code x maps it to; x itself
# when no row does
def sp_case(rows: List<&2, SpCase>, +x: U32) -> String:
  match rows:
    case Nil{}:
      SCon{Chr{x}, SNil{}}
    case r <> t:
      match r:
        case SpCaseRun{lo, hi, by}:
          sp_case.pick(Bool.and(U32.is_le(lo, x), U32.is_le(x, hi)), SCon{Chr{U32.add(x, by)}, SNil{}}, sp_case(t, x))
        case SpCaseOne{c, to}:
          sp_case.pick(U32.is_eq(x, c), to, sp_case(t, x))

# R4: each char of s mapped by the rows
def sp_case_str(+rows: List<&2, SpCase>, s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      String.append(sp_case(rows, Char.to_u32(c)), sp_case_str(rows, t))

# R4: the text folded: each char by CaseFolding.txt
def sp_fold(s: String) -> String:
  sp_case_str(sp_case_folding(), s)

# R4: the text lowered: each char by UnicodeData.txt and SpecialCasing.txt
def sp_lower(s: String) -> String:
  sp_case_str(sp_lowercase(), s)

# R5: the alternative its is found in s: anchored, s begins with a part
# that matches it (R2); else some part of s matches it
def SpFound(a: Bool, s: String, its: List<&2, Tp.It>) -> Type:
  match a:
    case True{}:
      Sigma<&1, &1, String, u => Sigma<&1, &1, String, r => {s == String.append(u, r) : String} & {sp_lang(u, its) == True{} : Bool}>>
    case False{}:
      Sigma<&1, &1, String, x => Sigma<&1, &1, String, u => Sigma<&1, &1, String, r => {s == String.append(x, String.append(u, r)) : String} & {sp_lang(u, its) == True{} : Bool}>>>

# The Bool searches below restate the code's search over the prefix test
# Tp.pm and the search Tp.occ; they are kept because laws/overflow.bend,
# laws/stream_failure.bend and their proofs read the tables through them
# (text_pat_any, text_pat_hit). R5 itself is stated by text_pat_hit_* and
# text_pat_any_* with SpFound.
def sp_found(anchored: Bool, +s: String, its: List<&2, Tp.It>) -> Bool:
  match anchored:
    case True{}:
      Tp.pm(s, its)
    case False{}:
      Tp.occ(s, its)

def sp_alts(+anchored: Bool, +s: String, alts: List<&2, List<&2, Tp.It>>) -> Bool:
  match alts:
    case Nil{}:
      False{}
    case its <> more:
      Bool.or(sp_found(anchored, s, its), sp_alts(anchored, s, more))

def sp_any(+s: String, ps: List<&2, Tp.Pat>) -> Bool:
  match ps:
    case Nil{}:
      False{}
    case p <> more:
      match p:
        case Tp.Pat{a, alts}:
          Bool.or(sp_alts(a, s, alts), sp_any(s, more))

# Laws
# ----

# LAW text_pat_class_table (R1): every char is of a class exactly when R1's
# table holds it: a literal's own code point; every code point but the line
# feed for `.`; 0030..0039 for a digit, with 002C for digit-or-comma; the
# White_Space rows of PropList.txt for a space
# EXCLUDES: `.` that matches a line feed, `\s` that misses a Unicode space
#   (U+0085, U+3000, the U+2000 run's ends) or takes a char that is none, a
#   digit class that takes a letter or misses `0` or `9`, a comma refused
#   by digit-or-comma
law text_pat_class_table:
  for k: Tp.Cls
  for +x: Char
  {Tp.is1(k, x) == sp_cls(k, x) : Bool}

# LAW text_pat_class_lit_self (R1): a literal class holds its own char
# EXCLUDES: a literal that refuses itself
law text_pat_class_lit_self:
  for +c: Char
  {Tp.is1(Tp.CLit{c}, c) == True{} : Bool}

# LAW text_pat_class_lit (R1): a char a literal class holds is that char
# EXCLUDES: a literal compared case-insensitively or by any looser test
law text_pat_class_lit:
  for +c: Char
  for +x: Char
  for h: {Tp.is1(Tp.CLit{c}, x) == True{} : Bool}
  {x == c : Char}

# LAW text_pat_prefix_complete (R2, R3): a text that begins with a part
# that matches the items passes the prefix test, whatever follows
# EXCLUDES: a missed match (a run that stops too early or too late, a
#   char of the class refused)
law text_pat_prefix_complete:
  for +u: String
  for +its: List<&2, Tp.It>
  for +rest: String
  for h: {sp_lang(u, its) == True{} : Bool}
  {Tp.pm(String.append(u, rest), its) == True{} : Bool}

# LAW text_pat_prefix_sound (R2, R3): a text that passes the prefix test
# begins with a part that matches the items
# EXCLUDES: a match invented (an item skipped, a char of another class
#   taken)
law text_pat_prefix_sound:
  for +s: String
  for +its: List<&2, Tp.It>
  for h: {Tp.pm(s, its) == True{} : Bool}
  exs u: String
  exs rest: String
  {s == String.append(u, rest) : String} & {sp_lang(u, its) == True{} : Bool}

# LAW text_pat_search_complete (R2, R3): a text with a part that matches
# the items anywhere is found
# EXCLUDES: a search that looks only at the start, or skips a position
law text_pat_search_complete:
  for +a: String
  for +u: String
  for +b: String
  for +its: List<&2, Tp.It>
  for h: {sp_lang(u, its) == True{} : Bool}
  {Tp.occ(String.append(a, String.append(u, b)), its) == True{} : Bool}

# LAW text_pat_search_sound (R2, R3): a text that is found has a part
# that matches the items
# EXCLUDES: a found pattern that is in no part of the text
law text_pat_search_sound:
  for +s: String
  for +its: List<&2, Tp.It>
  for h: {Tp.occ(s, its) == True{} : Bool}
  exs a: String
  exs u: String
  exs b: String
  {s == String.append(a, String.append(u, b)) : String} & {sp_lang(u, its) == True{} : Bool}

# LAW text_pat_hit_sound (R5): a pattern found in a text has an
# alternative that is found there (SpFound: anchored, a prefix of the text
# matches it; else a part of the text)
# EXCLUDES: a pattern found by no alternative, an anchored pattern found
#   past the text's start
law text_pat_hit_sound:
  for +s: String
  for +a: Bool
  for +alts: List<&2, List<&2, Tp.It>>
  for h: {Tp.hit(s, Tp.Pat{a, alts}) == True{} : Bool}
  exs pre: List<&2, List<&2, Tp.It>>
  exs its: List<&2, Tp.It>
  exs post: List<&2, List<&2, Tp.It>>
  {alts == List.append(&2, List<&2, Tp.It>, pre, its <> post) : List<&2, List<&2, Tp.It>>} & SpFound(a, s, its)

# LAW text_pat_hit_complete (R5): a pattern one of whose alternatives is
# found in a text (SpFound) is found there, wherever the alternative sits
# among the others
# EXCLUDES: an alternative skipped (only the first tried, a later one
#   lost), an unanchored pattern looked for only at the start
law text_pat_hit_complete:
  for +s: String
  for +a: Bool
  for +pre: List<&2, List<&2, Tp.It>>
  for +its: List<&2, Tp.It>
  for +post: List<&2, List<&2, Tp.It>>
  for h: SpFound(a, s, its)
  {Tp.hit(s, Tp.Pat{a, List.append(&2, List<&2, Tp.It>, pre, its <> post)}) == True{} : Bool}

# LAW text_pat_any_sound (R5): a list of patterns found in a text has a
# pattern with an alternative found there (SpFound)
# EXCLUDES: a list found by no pattern of it
law text_pat_any_sound:
  for +s: String
  for +ps: List<&2, Tp.Pat>
  for h: {Tp.any(s, ps) == True{} : Bool}
  exs pre: List<&2, Tp.Pat>
  exs a: Bool
  exs apre: List<&2, List<&2, Tp.It>>
  exs its: List<&2, Tp.It>
  exs apost: List<&2, List<&2, Tp.It>>
  exs post: List<&2, Tp.Pat>
  {ps == List.append(&2, Tp.Pat, pre, Tp.Pat{a, List.append(&2, List<&2, Tp.It>, apre, its <> apost)} <> post) : List<&2, Tp.Pat>} & SpFound(a, s, its)

# LAW text_pat_any_complete (R5): a list of patterns, one of which has an
# alternative found in a text (SpFound), is found there
# EXCLUDES: a pattern of the list skipped, the search stopped at the first
#   pattern that fails
law text_pat_any_complete:
  for +s: String
  for +pre: List<&2, Tp.Pat>
  for +a: Bool
  for +apre: List<&2, List<&2, Tp.It>>
  for +its: List<&2, Tp.It>
  for +apost: List<&2, List<&2, Tp.It>>
  for +post: List<&2, Tp.Pat>
  for h: SpFound(a, s, its)
  {Tp.any(s, List.append(&2, Tp.Pat, pre, Tp.Pat{a, List.append(&2, List<&2, Tp.It>, apre, its <> apost)} <> post)) == True{} : Bool}

# LAW text_pat_any (R5): the code's lazy search of a list of patterns
# equals the Bool search sp_any (a restatement over the code's own Tp.pm
# and Tp.occ, kept for laws/overflow.bend and its proofs; R5 is
# text_pat_any_sound and text_pat_any_complete)
# EXCLUDES: the lazy `or` of the code answering otherwise than the Bool
#   `or`
law text_pat_any:
  for +s: String
  for +ps: List<&2, Tp.Pat>
  {Tp.any(s, ps) == sp_any(s, ps) : Bool}

# LAW text_pat_hit (R5): the code's search of one pattern equals the Bool
# search sp_any of the list of it alone (kept for laws/overflow.bend,
# laws/stream_failure.bend and their proofs; R5 is text_pat_hit_sound and
# text_pat_hit_complete)
# EXCLUDES: a single pattern looked for another way than in a list
law text_pat_hit:
  for +s: String
  for +p: Tp.Pat
  {Tp.hit(s, p) == sp_any(s, [p]) : Bool}

# LAW text_pat_fold (R4): every text folds char by char as the
# CaseFolding.txt rows say (sp_case_folding: A-Z, U+017F, U+212A), every
# char no row holds kept as it is
# EXCLUDES: a fold that misses the Kelvin sign or the long s, folds
#   another char (a-z, `@`, `[`, U+0130), or shifts a char that is no
#   capital letter
law text_pat_fold:
  for s: String
  {Tp.fold_str(s) == sp_fold(s) : String}

# LAW text_pat_lower (R4): every text lowers char by char as the
# UnicodeData.txt and SpecialCasing.txt rows say (sp_lowercase: A-Z,
# U+0130 to two chars, U+212A), every char no row holds kept as it is
# EXCLUDES: a lowered capital I with dot of one char (Rust writes two), a
#   missed Kelvin sign, a lowered char that is no capital letter, the long
#   s lowered (it is lowercase already)
law text_pat_lower:
  for s: String
  {Tp.lower(s) == sp_lower(s) : String}

# LAW text_pat_example (R1-R4): anchor: a run of digits, a `.*` across a
# text, a line feed `.` refuses, a Unicode space, a folded Kelvin sign
# EXCLUDES: a spec that drifts from the regex it replaced
law text_pat_example:
  {[Tp.occ("max 12 tokens", [Tp.One{Tp.CDig{}}, Tp.Star{Tp.CDig{}}, Tp.One{Tp.CLit{' '}}, Tp.One{Tp.CLit{'t'}}]), Tp.occ(SCon{'a', SCon{'b', SCon{'\n', "c"}}}, [Tp.One{Tp.CLit{'a'}}, Tp.Star{Tp.CAny{}}, Tp.One{Tp.CLit{'c'}}]), Tp.pm(SCon{'4', SCon{Chr{8195}, "("}}, [Tp.One{Tp.CLit{'4'}}, Tp.Star{Tp.CSp{}}, Tp.One{Tp.CLit{'('}}]), Tp.occ(Tp.fold_str(SCon{'T', SCon{Chr{8490}, "N"}}), [Tp.One{Tp.CLit{'t'}}, Tp.One{Tp.CLit{'k'}}, Tp.One{Tp.CLit{'n'}}]), Tp.occ(Tp.lower(SCon{Chr{304}, "D"}), [Tp.One{Tp.CLit{'i'}}, Tp.One{Tp.CLit{'d'}}])] == [True{}, False{}, True{}, True{}, False{}] : List<&2, Bool>}
