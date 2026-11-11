# eukhe: the laws of area phrase

import Base
import ../bend/phrase.bend as P

# (P1) An explicit phrase search
# ------------------------------
# bend/phrase.bend: the search the error-text rules run instead of Rust
# `regex` patterns (no entry of its own: the entries of those rules call
# it). Every text, every class, every list of items and every edge is free.
#
# R1: a char is of a class exactly when: CIn lo hi, its code is from lo to
#     hi, both in; COut cs, it is none of the chars cs.
# R2: a word char is an ASCII letter (A-Z, a-z), an ASCII digit (0-9) or
#     `_`; every other char (past ASCII too) is no word char. (Rust's `\b`
#     takes the Unicode word chars: an intended difference.)
# R3: a text matches a list of items when it splits into one part per
#     item, in order: one char of the class for `One`, one char of the
#     class or the empty part for `Opt`, any run of chars of the class (the
#     empty run too) for `Star`.
# R4: the edge of a phrase on one side holds for the text on that side:
#     `EFree` always; `EWord` when that text is empty, or its char next to
#     the phrase (the last char of the text before, the first char of the
#     text after) is no word char; `EText` when that text is empty.
# R5: the prefix test of a text with an end edge is true exactly when the
#     text is a part that matches the items, then a rest the end edge holds
#     for; a phrase is found in a text exactly when the text is a text
#     before, then a part that matches its items, then a text after, its
#     start edge holding for the text before and its end edge for the text
#     after; a list of phrases is found when one of them is.

# Spec helpers
# ------------

def sp_code_in(+x: U32, lo: U32, hi: U32) -> Bool:
  Bool.and(U32.is_le(lo, x), U32.is_le(x, hi))

# R1: the code x is none of the codes of cs
def sp_none(cs: List<&2, Char>, +x: U32) -> Bool:
  match cs:
    case Nil{}:
      True{}
    case c <> t:
      Bool.and(Bool.not(U32.is_eq(Char.to_u32(c), x)), sp_none(t, x))

# R1: the chars of a class
def sp_cls(k: P.Cls, x: Char) -> Bool:
  match k:
    case P.CIn{lo, hi}:
      sp_code_in(Char.to_u32(x), lo, hi)
    case P.COut{cs}:
      sp_none(cs, Char.to_u32(x))

# R2: a word char: a-z (97-122), A-Z (65-90), 0-9 (48-57) or `_` (95)
def sp_word(x: Char) -> Bool:
  +v = Char.to_u32(x)
  Bool.or(sp_code_in(v, 97, 122), Bool.or(sp_code_in(v, 65, 90), Bool.or(sp_code_in(v, 48, 57), U32.is_eq(v, 95))))

# R3: the text u, whole, matches the items its
def sp_lang(u: String, its: List<&2, P.It>) -> Bool:
  match u:
    case SNil{}:
      match its:
        case Nil{}:
          True{}
        case i <> k:
          match i:
            case P.One{c}:
              False{}
            case P.Opt{c}:
              sp_lang(SNil{}, k)
            case P.Star{c}:
              sp_lang(SNil{}, k)
    case SCon{+x, +t}:
      match its:
        case Nil{}:
          False{}
        case i <> +k:
          match i:
            case P.One{c}:
              Bool.and(sp_cls(c, x), sp_lang(t, k))
            case P.Opt{c}:
              Bool.or(sp_lang(SCon{x, t}, k), Bool.and(sp_cls(c, x), sp_lang(t, k)))
            case P.Star{+c}:
              Bool.or(sp_lang(SCon{x, t}, k), Bool.and(sp_cls(c, x), sp_lang(t, P.Star{c} <> k)))

# R4: the end edge e holds for the text b after the part
def sp_end_ok(e: P.Edge, b: String) -> Bool:
  match e:
    case P.EFree{}:
      True{}
    case P.EWord{}:
      match b:
        case SNil{}:
          True{}
        case SCon{x, t}:
          Bool.not(sp_word(x))
    case P.EText{}:
      String.is_empty(b)

# R4: the text a is empty or its last char is no word char
def sp_last_free(a: String) -> Bool:
  match a:
    case SNil{}:
      True{}
    case SCon{x, t}:
      match t:
        case SNil{}:
          Bool.not(sp_word(x))
        case SCon{y, w}:
          sp_last_free(SCon{y, w})

# R4: the start edge e holds for the text a before the part
def sp_start_ok(e: P.Edge, a: String) -> Bool:
  match e:
    case P.EFree{}:
      True{}
    case P.EWord{}:
      sp_last_free(a)
    case P.EText{}:
      String.is_empty(a)

# R5: whether one of the phrases is found in s, phrase by phrase. P.found is
# the code's, pinned for every text and phrase by phrase_search_sound and
# phrase_search_complete: true exactly when R5's split exists. (P.any is
# another algorithm: one pass over the text, every phrase tried at each
# place.)
def sp_any(+s: String, phs: List<&2, P.Ph>) -> Bool:
  match phs:
    case Nil{}:
      False{}
    case p <> more:
      Bool.or(P.found(s, p), sp_any(s, more))

# Laws
# ----

# the phrase `x` followed by a whole-word edge: found in `x` then c exactly
# when c is no word char (R2)
def sp_x_word() -> P.Ph:
  P.Ph{P.EFree{}, [P.One{P.CIn{120, 120}}], P.EWord{}}

# LAW phrase_class_example (R1, R2): anchor: the boundaries of the ASCII word
# chars, as Rust regex-syntax's ASCII `\w` class [0-9A-Za-z_] draws them
# ('/' ':' '@' '[' '`' '{' around the ranges, '_' inside), two non-ASCII
# chars (U+00E9, and U+0660, a Unicode digit) outside; a CIn range at and
# past both its ends; COut refusing each listed char
# EXCLUDES: a word range off by one at either end, `_` left out, Unicode
#   letters or digits read as word chars, a range end left out, a listed
#   char taken by COut
law phrase_class_example:
  {[P.found("x/", sp_x_word()), P.found("x0", sp_x_word()), P.found("x9", sp_x_word()), P.found("x:", sp_x_word()), P.found("x@", sp_x_word()), P.found("xA", sp_x_word()), P.found("xZ", sp_x_word()), P.found("x[", sp_x_word()), P.found("x`", sp_x_word()), P.found("xa", sp_x_word()), P.found("xz", sp_x_word()), P.found("x{", sp_x_word()), P.found("x_", sp_x_word()), P.found(SCon{'x', SCon{Chr{233}, ""}}, sp_x_word()), P.found(SCon{'x', SCon{Chr{1632}, ""}}, sp_x_word()), P.found("a", P.Ph{P.EFree{}, [P.One{P.CIn{98, 100}}], P.EFree{}}), P.found("b", P.Ph{P.EFree{}, [P.One{P.CIn{98, 100}}], P.EFree{}}), P.found("d", P.Ph{P.EFree{}, [P.One{P.CIn{98, 100}}], P.EFree{}}), P.found("e", P.Ph{P.EFree{}, [P.One{P.CIn{98, 100}}], P.EFree{}}), P.found("b", P.Ph{P.EFree{}, [P.One{P.COut{['b', 'c']}}], P.EFree{}}), P.found("c", P.Ph{P.EFree{}, [P.One{P.COut{['b', 'c']}}], P.EFree{}}), P.found("d", P.Ph{P.EFree{}, [P.One{P.COut{['b', 'c']}}], P.EFree{}})] == [True{}, False{}, False{}, True{}, True{}, False{}, False{}, True{}, True{}, False{}, False{}, True{}, False{}, True{}, True{}, False{}, True{}, True{}, False{}, False{}, False{}, True{}] : List<&2, Bool>}

# LAW phrase_prefix_complete (R3-R5): a text that begins with a part that
# matches the items, followed by a rest the end edge holds for, passes the
# prefix test
# EXCLUDES: a missed match (an optional char that must be taken or must be
#   skipped, a run that stops too early or too late, a char of the class
#   refused), an end edge refused where it holds
law phrase_prefix_complete:
  for +u: String
  for +its: List<&2, P.It>
  for +rest: String
  for +end: P.Edge
  for h: {sp_lang(u, its) == True{} : Bool}
  for he: {sp_end_ok(end, rest) == True{} : Bool}
  {P.pm(String.append(u, rest), its, end) == True{} : Bool}

# LAW phrase_prefix_sound (R3-R5): a text that passes the prefix test
# begins with a part that matches the items, followed by a rest the end
# edge holds for
# EXCLUDES: a match invented (an item skipped, a char of another class
#   taken), a whole word that continues into a word char, a text end that
#   is no end
law phrase_prefix_sound:
  for +s: String
  for +its: List<&2, P.It>
  for +end: P.Edge
  for h: {P.pm(s, its, end) == True{} : Bool}
  exs u: String
  exs rest: String
  {s == String.append(u, rest) : String} & ({sp_lang(u, its) == True{} : Bool} & {sp_end_ok(end, rest) == True{} : Bool})

# LAW phrase_search_complete (R3-R5): a text with a part that matches the
# items, its start edge holding for the text before and its end edge for
# the text after, is found
# EXCLUDES: a search that looks only at the start, skips a place, or
#   refuses a whole word after a non-word char (or at the text start)
law phrase_search_complete:
  for +a: String
  for +u: String
  for +b: String
  for +st: P.Edge
  for +its: List<&2, P.It>
  for +en: P.Edge
  for h: {sp_lang(u, its) == True{} : Bool}
  for hs: {sp_start_ok(st, a) == True{} : Bool}
  for he: {sp_end_ok(en, b) == True{} : Bool}
  {P.found(String.append(a, String.append(u, b)), P.Ph{st, its, en}) == True{} : Bool}

# LAW phrase_search_sound (R3-R5): a text in which a phrase is found is a
# text before, a part that matches the items and a text after, with the
# start edge holding for the text before and the end edge for the text
# after
# EXCLUDES: a phrase found in no part of the text, a whole word found
#   inside a longer word (a digit code inside a longer number), a text
#   start found in the middle
law phrase_search_sound:
  for +s: String
  for +st: P.Edge
  for +its: List<&2, P.It>
  for +en: P.Edge
  for h: {P.found(s, P.Ph{st, its, en}) == True{} : Bool}
  exs a: String
  exs u: String
  exs b: String
  {s == String.append(a, String.append(u, b)) : String} & ({sp_lang(u, its) == True{} : Bool} & ({sp_start_ok(st, a) == True{} : Bool} & {sp_end_ok(en, b) == True{} : Bool}))

# LAW phrase_any (R5): a list of phrases is found in every text exactly
# when one of them is: the code's one-pass search (every phrase tried at
# each place) equals the search phrase by phrase with P.found, which the
# phrase_search_* laws pin to R5's split
# EXCLUDES: a phrase of the list skipped, a list found by a phrase it does
#   not hold, a place skipped for a later phrase after an earlier one failed
law phrase_any:
  for +s: String
  for +phs: List<&2, P.Ph>
  {P.any(s, phs) == sp_any(s, phs) : Bool}

# LAW phrase_example (R1-R5): anchor: a whole word at the text start and
# at its end, `_` as a word char, a digit code inside a longer number
# refused, an optional char taken and skipped, COut refusing a listed char,
# text edges
# EXCLUDES: a search that drifts from the regexes it replaced
law phrase_example:
  {[P.found("ab c", P.Ph{P.EWord{}, [P.One{P.CIn{97, 97}}, P.One{P.CIn{98, 98}}], P.EWord{}}), P.found("c ab", P.Ph{P.EWord{}, [P.One{P.CIn{97, 97}}, P.One{P.CIn{98, 98}}], P.EWord{}}), P.found("ab_", P.Ph{P.EWord{}, [P.One{P.CIn{97, 97}}, P.One{P.CIn{98, 98}}], P.EWord{}}), P.found("1429", P.Ph{P.EWord{}, [P.One{P.CIn{52, 52}}, P.One{P.CIn{50, 50}}], P.EFree{}}), P.found("a-b", P.Ph{P.EFree{}, [P.One{P.CIn{97, 97}}, P.Opt{P.COut{['\n']}}, P.One{P.CIn{98, 98}}], P.EFree{}}), P.found("ab", P.Ph{P.EFree{}, [P.One{P.CIn{97, 97}}, P.Opt{P.COut{['\n']}}, P.One{P.CIn{98, 98}}], P.EFree{}}), P.found(SCon{'a', SCon{'\n', "b"}}, P.Ph{P.EFree{}, [P.One{P.CIn{97, 97}}, P.Opt{P.COut{['\n']}}, P.One{P.CIn{98, 98}}], P.EFree{}}), P.found("ba", P.Ph{P.EText{}, [P.One{P.CIn{97, 97}}], P.EFree{}}), P.found("ab", P.Ph{P.EText{}, [P.One{P.CIn{97, 97}}], P.EFree{}}), P.found("ab", P.Ph{P.EFree{}, [P.One{P.CIn{97, 97}}], P.EText{}})] == [True{}, True{}, False{}, False{}, True{}, True{}, False{}, False{}, True{}, False{}] : List<&2, Bool>}
