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
#     U+205F, U+3000).
# R2: a text matches a list of items when it splits into one part per
#     item, in order: one char of the class for `One`, any run of chars of
#     the class (the empty run too) for `Star`.
# R3: the prefix test of a text is true exactly when some prefix of the
#     text matches the items; the search is true exactly when some part of
#     the text (a prefix of a suffix) matches them.
# R4: `fold` maps A-Z to a-z, the Kelvin sign U+212A to k and the long s
#     U+017F to s, every other char to itself (Unicode simple case folding
#     as far as it reaches a lowercase ASCII char: a case-insensitive regex
#     matches a lowercase ASCII pattern char exactly where the folded text
#     holds it). `lower` maps A-Z to a-z, U+212A to k, the capital I with
#     dot U+0130 to i then U+0307, every other char to itself (Rust's
#     `to_lowercase` maps no other char to an ASCII letter, a line feed or
#     more than one char).
# R5: a pattern is found in a text when one of its alternatives is: at
#     the text's start for an anchored pattern (the prefix test), anywhere
#     else (the search); a list of patterns when one of them is.

# Spec helpers
# ------------

def sp_in(+x: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_le(lo, x), U32.is_le(x, hi))

# R1: Unicode White_Space, as ranges
def sp_ws_code(+x: U32) -> Bool:
  Bool.or(sp_in(x, 9, 13), Bool.or(U32.is_eq(x, 32), Bool.or(U32.is_eq(x, 133), Bool.or(U32.is_eq(x, 160), Bool.or(U32.is_eq(x, 5760), Bool.or(sp_in(x, 8192, 8202), Bool.or(U32.is_eq(x, 8232), Bool.or(U32.is_eq(x, 8233), Bool.or(U32.is_eq(x, 8239), Bool.or(U32.is_eq(x, 8287), U32.is_eq(x, 12288)))))))))))

def sp_digit_code(+x: U32) -> Bool:
  sp_in(x, 48, 57)

# R1: the chars of a class
def sp_cls(k: Tp.Cls, x: Char) -> Bool:
  match k:
    case Tp.CLit{c}:
      U32.is_eq(Char.to_u32(c), Char.to_u32(x))
    case Tp.CAny{}:
      Bool.not(U32.is_eq(Char.to_u32(x), 10))
    case Tp.CDig{}:
      sp_digit_code(Char.to_u32(x))
    case Tp.CDigC{}:
      +v = Char.to_u32(x)
      Bool.or(sp_digit_code(v), U32.is_eq(v, 44))
    case Tp.CSp{}:
      sp_ws_code(Char.to_u32(x))

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

# R4: the folded char of code x
def sp_fold_pick(+x: U32, upper: Bool, kelvin: Bool, longs: Bool) -> U32:
  match upper:
    case True{}:
      U32.add(x, 32)
    case False{}:
      match kelvin:
        case True{}:
          107
        case False{}:
          match longs:
            case True{}:
              115
            case False{}:
              x

def sp_fold_code(+x: U32) -> U32:
  sp_fold_pick(x, sp_in(x, 65, 90), U32.is_eq(x, 8490), U32.is_eq(x, 383))

def sp_fold(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      SCon{Chr{sp_fold_code(Char.to_u32(c))}, sp_fold(t)}

# R4: the lowered chars of the char of code x, before rest
def sp_lower_pick(+x: U32, upper: Bool, kelvin: Bool, idot: Bool) -> String:
  match upper:
    case True{}:
      SCon{Chr{U32.add(x, 32)}, SNil{}}
    case False{}:
      match kelvin:
        case True{}:
          SCon{Chr{107}, SNil{}}
        case False{}:
          match idot:
            case True{}:
              SCon{Chr{105}, SCon{Chr{775}, SNil{}}}
            case False{}:
              SCon{Chr{x}, SNil{}}

def sp_lower(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{c, t}:
      +x = Char.to_u32(c)
      String.append(sp_lower_pick(x, sp_in(x, 65, 90), U32.is_eq(x, 8490), U32.is_eq(x, 304)), sp_lower(t))

# R5: one alternative found in s: at its start (the prefix test), or in
# some part (the search)
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

# R5: whether one of the patterns is found in s: one of the alternatives
# of one of them
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

# LAW text_pat_class (R1): every char is of a class exactly as R1 says
# EXCLUDES: `.` that matches a line feed, `\s` that misses a Unicode space
#   or takes a char that is none, a digit class that takes a letter, a
#   literal compared case-insensitively
law text_pat_class:
  for k: Tp.Cls
  for +x: Char
  {Tp.is1(k, x) == sp_cls(k, x) : Bool}

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

# LAW text_pat_any (R5): a list of patterns is found in every text
# exactly when one alternative of one pattern is, by the prefix test for an
# anchored pattern and the search for the others
# EXCLUDES: an alternative or a pattern skipped, an anchored pattern
#   searched anywhere, an unanchored one only at the start
law text_pat_any:
  for +s: String
  for +ps: List<&2, Tp.Pat>
  {Tp.any(s, ps) == sp_any(s, ps) : Bool}

# LAW text_pat_hit (R5): one pattern is found in every text exactly when
# the list of it alone is
# EXCLUDES: a single pattern looked for another way than in a list
law text_pat_hit:
  for +s: String
  for +p: Tp.Pat
  {Tp.hit(s, p) == sp_any(s, [p]) : Bool}

# LAW text_pat_fold (R4): every text folds as R4 says
# EXCLUDES: a fold that misses the Kelvin sign or the long s, folds
#   another char, or shifts a char that is no capital letter
law text_pat_fold:
  for s: String
  {Tp.fold_str(s) == sp_fold(s) : String}

# LAW text_pat_lower (R4): every text lowers as R4 says
# EXCLUDES: a lowered capital I with dot of one char (Rust writes two), a
#   missed Kelvin sign, a lowered char that is no capital letter
law text_pat_lower:
  for s: String
  {Tp.lower(s) == sp_lower(s) : String}

# LAW text_pat_example (R1-R4): anchor: a run of digits, a `.*` across a
# text, a line feed `.` refuses, a Unicode space, a folded Kelvin sign
# EXCLUDES: a spec that drifts from the regex it replaced
law text_pat_example:
  {[Tp.occ("max 12 tokens", [Tp.One{Tp.CDig{}}, Tp.Star{Tp.CDig{}}, Tp.One{Tp.CLit{' '}}, Tp.One{Tp.CLit{'t'}}]), Tp.occ(SCon{'a', SCon{'b', SCon{'\n', "c"}}}, [Tp.One{Tp.CLit{'a'}}, Tp.Star{Tp.CAny{}}, Tp.One{Tp.CLit{'c'}}]), Tp.pm(SCon{'4', SCon{Chr{8195}, "("}}, [Tp.One{Tp.CLit{'4'}}, Tp.Star{Tp.CSp{}}, Tp.One{Tp.CLit{'('}}]), Tp.occ(Tp.fold_str(SCon{'T', SCon{Chr{8490}, "N"}}), [Tp.One{Tp.CLit{'t'}}, Tp.One{Tp.CLit{'k'}}, Tp.One{Tp.CLit{'n'}}]), Tp.occ(Tp.lower(SCon{Chr{304}, "D"}), [Tp.One{Tp.CLit{'i'}}, Tp.One{Tp.CLit{'d'}}])] == [True{}, False{}, True{}, True{}, False{}] : List<&2, Bool>}
