# eukhe: the laws of area model_name

import Base
import ../bend/model_name.bend as M
import ../bend/ffi_model_name.bend as FM
import ../bend/wire.bend as Wr
import ./base.bend as LawsBase

# (MN1) The name rules of the quirks rulebook
# -------------------------------------------
# bend/model_name.bend, run as the compiled core by bend/ffi_model_name.bend
# (eukhe-bend rules/model_name.rs; asked by eukhe-ai quirks/ for the
# rulebook's family `match`/`except` sets and price rows, in place of their
# `regex` patterns). Every rule, every list of strings, every name, every
# Nat and every flag is free. "p ++ q" is p then q.
#
# R1: contains ps: the name holds one of ps as a part (name = a ++ p ++ b,
#     p one of ps).
# R2: is ps: the name is one of ps.
# R3: starts ps: the name begins with one of ps (name = p ++ b).
# R4: then a b: the name holds a, and after it, on the same line, b: name =
#     x ++ a ++ y ++ b ++ z where y holds no line feed (U+000A).
# R5: number after least whole: the name begins with one of `after` (p); D
#     = the maximal run of ASCII digits right after p; after D's leading
#     zeros, D has two or more digits left, or exactly one digit whose value
#     is at least `least`; with whole, D ends the name or a `-` follows it.
#     As a split: name = p ++ z ++ d ++ r, z all `0`, d an ASCII digit 1-9
#     then ASCII digits, two or more chars or one of value at least
#     `least`, r empty or opening with no ASCII digit, and with whole r
#     empty or opening with `-`. (For every Nat `least`; the rulebook uses
#     1-9: "a number at least `least`".)
# R6: segment_starts ps: the part of the name after its last `/` (the whole
#     name when it has none) begins with one of ps: name = a ++ p ++ b, a
#     empty or ending with `/`, p ++ b without `/`.
# R7: a rule set holds for a group of names when one of its rules holds for
#     one of its names; the verdicts of sets over groups go group by group,
#     each group set by set.
# R8: dash: each maximal run of separators replaced by one `-`; a
#     separator is a Unicode White_Space char (the White_Space property of
#     the Unicode Character Database, PropList.txt; the `\s` of the Rust
#     regex `[\s_.:]+` this replaced), `_`, `.` or `:`.
# R9: the entry answers each request Rust writes (bend/ffi_model_name.bend
#     header: request 0 the sets, then the groups, reply the verdicts of
#     R7 as a list of Bool; request 1 the texts, reply each dashed; rule
#     tags 0 contains, 1 is, 2 starts, 3 then, 4 number, 5 segment_starts;
#     every count, length and Nat within the wire) with that answer, reads
#     exactly the request and nothing after it, and answers any other input
#     (a request tag past 1 or a rule tag past 5 too) with the exact error
#     form `E model_name: malformed request`.

# Spec helpers
# ------------

# the code of a char
def sp_code(x: Char) -> U32:
  Char.to_u32(x)

# x and y are the same char
def sp_eq(x: Char, y: Char) -> Bool:
  U32.is_eq(sp_code(x), sp_code(y))

# R3: s begins with p
def sp_pre(p: String, s: String) -> Bool:
  match p:
    case SNil{}:
      True{}
    case SCon{c, pt}:
      match s:
        case SNil{}:
          False{}
        case SCon{x, st}:
          Bool.and(sp_eq(c, x), sp_pre(pt, st))

# R2: s is p
def sp_same(p: String, s: String) -> Bool:
  match p:
    case SNil{}:
      String.is_empty(s)
    case SCon{c, pt}:
      match s:
        case SNil{}:
          False{}
        case SCon{x, st}:
          Bool.and(sp_eq(c, x), sp_same(pt, st))

# R5: an ASCII digit (48-57), `0` (48), the value of a digit
def sp_digit(x: Char) -> Bool:
  +v = sp_code(x)
  Bool.and(U32.is_le(48, v), U32.is_le(v, 57))

def sp_zero(x: Char) -> Bool:
  U32.is_eq(sp_code(x), 48)

def sp_value(x: Char) -> Nat:
  Nat.sub(U32.to_nat(sp_code(x)), 48n)

# R5: the char x that follows the run of digits: with whole, only `-` (45)
def sp_ends(w: Bool, x: Char) -> Bool:
  match w:
    case True{}:
      U32.is_eq(sp_code(x), 45)
    case False{}:
      True{}

# R6: s holds a `/` (47)
def sp_has_slash(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{x, t}:
      Bool.or(U32.is_eq(sp_code(x), 47), sp_has_slash(t))

def sp_pick(b: Bool, x: String, y: String) -> String:
  match b:
    case True{}:
      x
    case False{}:
      y

# R6: the part of s after its last `/` (s when it has none)
def sp_seg(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+x, +t}:
      sp_pick(sp_has_slash(t), sp_seg(t), sp_pick(U32.is_eq(sp_code(x), 47), t, SCon{x, t}))

# R4: y holds no line feed
def sp_no_lf(y: String) -> Bool:
  match y:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.and(Bool.not(U32.is_eq(sp_code(x), 10)), sp_no_lf(t))

# R5: z is all `0`
def sp_zeros(z: String) -> Bool:
  match z:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.and(sp_zero(x), sp_zeros(t))

# R5: d is all ASCII digits
def sp_digits(d: String) -> Bool:
  match d:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.and(sp_digit(x), sp_digits(t))

# R5: d is what is left of the run after its leading zeros, and passes: a
# digit 1-9, then digits; two or more, or one of value at least n
def sp_sig(d: String, n: Nat) -> Bool:
  match d:
    case SNil{}:
      False{}
    case SCon{+x, +t}:
      Bool.and(Bool.and(sp_digit(x), Bool.not(sp_zero(x))), Bool.and(sp_digits(t), Bool.or(Bool.not(String.is_empty(t)), Nat.is_le(n, sp_value(x)))))

# R5: r follows the run: it opens with no digit; with w, it is empty or
# opens with `-`
def sp_after(w: Bool, r: String) -> Bool:
  match r:
    case SNil{}:
      True{}
    case SCon{+x, t}:
      Bool.and(Bool.not(sp_digit(x)), sp_ends(w, x))

# R6: a is empty or ends with `/`
def sp_seg_start(a: String) -> Bool:
  match a:
    case SNil{}:
      True{}
    case SCon{x, t}:
      match t:
        case SNil{}:
          U32.is_eq(sp_code(x), 47)
        case SCon{y, u}:
          sp_seg_start(SCon{y, u})

# R7: the verdict rows of M.holds are pinned by the model_name_holds_*
# laws below; R8: M.dash by the model_name_dash_* laws.

# R8: the White_Space code points, one row per line of the White_Space
# entries of Unicode's PropList.txt (Unicode 15.1, unchanged since 6.3):
# 0009..000D, 0020, 0085, 00A0, 1680, 2000..200A, 2028, 2029, 202F, 205F,
# 3000
type SpWs is Data:
  SpWsOne{c: U32}
  SpWsRun{lo: U32, hi: U32}

def sp_ws_rows() -> List<&2, SpWs>:
  [SpWsRun{9, 13}, SpWsOne{32}, SpWsOne{133}, SpWsOne{160}, SpWsOne{5760}, SpWsRun{8192, 8202}, SpWsOne{8232}, SpWsOne{8233}, SpWsOne{8239}, SpWsOne{8287}, SpWsOne{12288}]

# the code x is in the row w
def sp_ws_in(+x: U32, w: SpWs) -> Bool:
  match w:
    case SpWsOne{c}:
      U32.is_eq(x, c)
    case SpWsRun{lo, hi}:
      Bool.and(U32.is_le(lo, x), U32.is_le(x, hi))

def sp_ws_any.at(t: List<&2, SpWs>, w: SpWs, +x: U32) -> Bool:
  match t:
    case Nil{}:
      sp_ws_in(x, w)
    case v <> u:
      Bool.or(sp_ws_in(x, w), sp_ws_any.at(u, v, x))

def sp_ws_any(+x: U32, ws: List<&2, SpWs>) -> Bool:
  match ws:
    case Nil{}:
      False{}
    case w <> t:
      sp_ws_any.at(t, w, x)

# R8: the code x is a White_Space code point (in one of the rows)
def sp_ws(+x: U32) -> Bool:
  sp_ws_any(x, sp_ws_rows())

# R8: a separator: White_Space, `_` (95), `.` (46) or `:` (58)
def sp_sep(c: Char) -> Bool:
  match c:
    case Chr{+x}:
      Bool.or(sp_ws(x), Bool.or(U32.is_eq(x, 95), Bool.or(U32.is_eq(x, 46), U32.is_eq(x, 58))))

# R8: s holds no separator
def sp_no_sep(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.and(Bool.not(sp_sep(x)), sp_no_sep(t))

# R8: every char of s is a separator
def sp_all_sep(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.and(sp_sep(x), sp_all_sep(t))

# R8: a is empty or its last char is no separator
def sp_ends_free(a: String) -> Bool:
  match a:
    case SNil{}:
      True{}
    case SCon{x, t}:
      match t:
        case SNil{}:
          Bool.not(sp_sep(x))
        case SCon{y, u}:
          sp_ends_free(SCon{y, u})

# R8: b is empty or its first char is no separator
def sp_starts_free(b: String) -> Bool:
  match b:
    case SNil{}:
      True{}
    case SCon{x, t}:
      Bool.not(sp_sep(x))

# R9: each text of ts dashed by M.dash, in order
def sp_dash_all(ts: List<&2, String>) -> List<&2, String>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> more:
      M.dash(t) <> sp_dash_all(more)

# R9: the spelling of a request and of its reply

def sp_w_rule(r: M.Rule, rest: String) -> String:
  match r:
    case M.RContains{ps}:
      Wr.put_nat(0n, LawsBase.wire_spell_strs(ps, rest))
    case M.RIs{ps}:
      Wr.put_nat(1n, LawsBase.wire_spell_strs(ps, rest))
    case M.RStarts{ps}:
      Wr.put_nat(2n, LawsBase.wire_spell_strs(ps, rest))
    case M.RThen{a, b}:
      Wr.put_nat(3n, Wr.put_str(a, Wr.put_str(b, rest)))
    case M.RNumber{ps, n, w}:
      Wr.put_nat(4n, LawsBase.wire_spell_strs(ps, Wr.put_nat(n, Wr.put_bool(w, rest))))
    case M.RSegment{ps}:
      Wr.put_nat(5n, LawsBase.wire_spell_strs(ps, rest))

def sp_w_rules.items(rs: List<&2, M.Rule>, rest: String) -> String:
  match rs:
    case Nil{}:
      rest
    case r <> more:
      sp_w_rule(r, sp_w_rules.items(more, rest))

def sp_w_rules(+rs: List<&2, M.Rule>, rest: String) -> String:
  Wr.put_nat(List.length(&2, M.Rule, rs), sp_w_rules.items(rs, rest))

def sp_w_sets.items(sets: List<&2, List<&2, M.Rule>>, rest: String) -> String:
  match sets:
    case Nil{}:
      rest
    case rs <> more:
      sp_w_rules(rs, sp_w_sets.items(more, rest))

def sp_w_sets(+sets: List<&2, List<&2, M.Rule>>, rest: String) -> String:
  Wr.put_nat(List.length(&2, List<&2, M.Rule>, sets), sp_w_sets.items(sets, rest))

def sp_w_groups.items(gs: List<&2, List<&2, String>>, rest: String) -> String:
  match gs:
    case Nil{}:
      rest
    case g <> more:
      LawsBase.wire_spell_strs(g, sp_w_groups.items(more, rest))

def sp_w_groups(+gs: List<&2, List<&2, String>>, rest: String) -> String:
  Wr.put_nat(List.length(&2, List<&2, String>, gs), sp_w_groups.items(gs, rest))

def sp_w_req(q: FM.Req, rest: String) -> String:
  match q:
    case FM.QHolds{sets, gs}:
      Wr.put_nat(0n, sp_w_sets(sets, sp_w_groups(gs, rest)))
    case FM.QDash{ts}:
      Wr.put_nat(1n, LawsBase.wire_spell_strs(ts, rest))

def sp_w_bools.items(bs: List<&2, Bool>, rest: String) -> String:
  match bs:
    case Nil{}:
      rest
    case b <> more:
      Wr.put_bool(b, sp_w_bools.items(more, rest))

def sp_w_bools(+bs: List<&2, Bool>, rest: String) -> String:
  Wr.put_nat(List.length(&2, Bool, bs), sp_w_bools.items(bs, rest))

def sp_w_reply(q: FM.Req) -> String:
  match q:
    case FM.QHolds{sets, gs}:
      sp_w_bools(M.holds(sets, gs), "")
    case FM.QDash{ts}:
      LawsBase.wire_spell_strs(sp_dash_all(ts), "")

# every count, length and Nat of a rule, a set, the sets, the groups and a
# request fits the wire
def sp_fit_rule(r: M.Rule) -> Bool:
  match r:
    case M.RContains{ps}:
      LawsBase.wire_strs_fit(ps)
    case M.RIs{ps}:
      LawsBase.wire_strs_fit(ps)
    case M.RStarts{ps}:
      LawsBase.wire_strs_fit(ps)
    case M.RThen{a, b}:
      Bool.and(LawsBase.wire_fits(String.length(a)), LawsBase.wire_fits(String.length(b)))
    case M.RNumber{ps, n, w}:
      Bool.and(LawsBase.wire_strs_fit(ps), LawsBase.wire_fits(n))
    case M.RSegment{ps}:
      LawsBase.wire_strs_fit(ps)

def sp_fit_rules(rs: List<&2, M.Rule>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> more:
      Bool.and(sp_fit_rule(r), sp_fit_rules(more))

def sp_fit_set(+rs: List<&2, M.Rule>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, M.Rule, rs)), sp_fit_rules(rs))

def sp_fit_sets.all(sets: List<&2, List<&2, M.Rule>>) -> Bool:
  match sets:
    case Nil{}:
      True{}
    case rs <> more:
      Bool.and(sp_fit_set(rs), sp_fit_sets.all(more))

def sp_fit_sets(+sets: List<&2, List<&2, M.Rule>>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, List<&2, M.Rule>, sets)), sp_fit_sets.all(sets))

def sp_fit_groups.all(gs: List<&2, List<&2, String>>) -> Bool:
  match gs:
    case Nil{}:
      True{}
    case g <> more:
      Bool.and(LawsBase.wire_strs_fit(g), sp_fit_groups.all(more))

def sp_fit_groups(+gs: List<&2, List<&2, String>>) -> Bool:
  Bool.and(LawsBase.wire_fits(List.length(&2, List<&2, String>, gs)), sp_fit_groups.all(gs))

def sp_fit_req(q: FM.Req) -> Bool:
  match q:
    case FM.QHolds{sets, gs}:
      Bool.and(sp_fit_sets(sets), sp_fit_groups(gs))
    case FM.QDash{ts}:
      LawsBase.wire_strs_fit(ts)

# Laws: the rules
# ---------------

# LAW model_name_contains_complete (R1): a name that holds one of ps as a
# part, anywhere, passes contains ps
# EXCLUDES: a part looked for only at the start or the end, a string of ps
#   skipped, text around the part that hides it
law model_name_contains_complete:
  for +pre: List<&2, String>
  for +p: String
  for +post: List<&2, String>
  for +a: String
  for +b: String
  {M.rule(M.RContains{List.append(&2, String, pre, p <> post)}, String.append(a, String.append(p, b))) == True{} : Bool}

# LAW model_name_contains_sound (R1): a name that passes contains ps holds
# one of ps as a part
# EXCLUDES: a part matched loosely (case, a char skipped), a hit with no
#   string of ps in the name
law model_name_contains_sound:
  for +ps: List<&2, String>
  for +s: String
  for h: {M.rule(M.RContains{ps}, s) == True{} : Bool}
  exs pre: List<&2, String>
  exs p: String
  exs post: List<&2, String>
  exs a: String
  exs b: String
  {ps == List.append(&2, String, pre, p <> post) : List<&2, String>} & {s == String.append(a, String.append(p, b)) : String}

# LAW model_name_is_complete (R2): a name that is one of ps passes is ps
# EXCLUDES: a string of ps skipped
law model_name_is_complete:
  for +pre: List<&2, String>
  for +s: String
  for +post: List<&2, String>
  {M.rule(M.RIs{List.append(&2, String, pre, s <> post)}, s) == True{} : Bool}

# LAW model_name_is_sound (R2): a name that passes is ps is one of ps
# EXCLUDES: a prefix or an extension of a string of ps taken as it
law model_name_is_sound:
  for +ps: List<&2, String>
  for +s: String
  for h: {M.rule(M.RIs{ps}, s) == True{} : Bool}
  exs pre: List<&2, String>
  exs post: List<&2, String>
  {ps == List.append(&2, String, pre, s <> post) : List<&2, String>}

# LAW model_name_starts_complete (R3): a name that begins with one of ps
# passes starts ps
# EXCLUDES: a string of ps skipped, a prefix refused when more follows
law model_name_starts_complete:
  for +pre: List<&2, String>
  for +p: String
  for +post: List<&2, String>
  for +b: String
  {M.rule(M.RStarts{List.append(&2, String, pre, p <> post)}, String.append(p, b)) == True{} : Bool}

# LAW model_name_starts_sound (R3): a name that passes starts ps begins
# with one of ps
# EXCLUDES: a string of ps found past the start
law model_name_starts_sound:
  for +ps: List<&2, String>
  for +s: String
  for h: {M.rule(M.RStarts{ps}, s) == True{} : Bool}
  exs pre: List<&2, String>
  exs p: String
  exs post: List<&2, String>
  exs b: String
  {ps == List.append(&2, String, pre, p <> post) : List<&2, String>} & {s == String.append(p, b) : String}

# LAW model_name_then_complete (R4): a name that holds a, and after it on
# the same line b, passes then a b
# EXCLUDES: only the first place of a tried, b required right after a, a
#   text between that hides the hit
law model_name_then_complete:
  for +a: String
  for +b: String
  for +x: String
  for +y: String
  for +z: String
  for h: {sp_no_lf(y) == True{} : Bool}
  {M.rule(M.RThen{a, b}, String.append(x, String.append(a, String.append(y, String.append(b, z))))) == True{} : Bool}

# LAW model_name_then_sound (R4): a name that passes then a b holds a, and
# after it on the same line b
# EXCLUDES: b before a, b across a line feed, a and b swapped or
#   overlapping
law model_name_then_sound:
  for +a: String
  for +b: String
  for +s: String
  for h: {M.rule(M.RThen{a, b}, s) == True{} : Bool}
  exs x: String
  exs y: String
  exs z: String
  {s == String.append(x, String.append(a, String.append(y, String.append(b, z)))) : String} & {sp_no_lf(y) == True{} : Bool}

# LAW model_name_number_complete (R5): a name that begins with one of
# `after`, then leading zeros, then a passing run of digits, then a rest
# that ends the run (with whole: nothing or `-`), passes number
# EXCLUDES: leading zeros counted as digits or refused, a run read only
#   in part, a digit compared off by one, whole refusing `-`
law model_name_number_complete:
  for +pre: List<&2, String>
  for +p: String
  for +post: List<&2, String>
  for +z: String
  for +d: String
  for +r: String
  for +n: Nat
  for +w: Bool
  for hz: {sp_zeros(z) == True{} : Bool}
  for hd: {sp_sig(d, n) == True{} : Bool}
  for hr: {sp_after(w, r) == True{} : Bool}
  {M.rule(M.RNumber{List.append(&2, String, pre, p <> post), n, w}, String.append(p, String.append(z, String.append(d, r)))) == True{} : Bool}

# LAW model_name_number_sound (R5): a name that passes number begins with
# one of `after`, leading zeros, a passing run of digits and a rest that
# ends it
# EXCLUDES: a run cut before its end (gpt-5.10.1 read as 10 with whole), a
#   single digit below the least, zeros alone, a non-digit after the run
#   with whole
law model_name_number_sound:
  for +ps: List<&2, String>
  for +s: String
  for +n: Nat
  for +w: Bool
  for h: {M.rule(M.RNumber{ps, n, w}, s) == True{} : Bool}
  exs pre: List<&2, String>
  exs p: String
  exs post: List<&2, String>
  exs z: String
  exs d: String
  exs r: String
  {ps == List.append(&2, String, pre, p <> post) : List<&2, String>} & ({s == String.append(p, String.append(z, String.append(d, r))) : String} & ({sp_zeros(z) == True{} : Bool} & ({sp_sig(d, n) == True{} : Bool} & {sp_after(w, r) == True{} : Bool})))

# LAW model_name_segment_complete (R6): a name whose part after its last
# `/` begins with one of ps passes segment_starts ps
# EXCLUDES: only names with a `/` (or only without) read, a segment that
#   is not the last
law model_name_segment_complete:
  for +pre: List<&2, String>
  for +p: String
  for +post: List<&2, String>
  for +a: String
  for +b: String
  for ha: {sp_seg_start(a) == True{} : Bool}
  for hb: {sp_has_slash(String.append(p, b)) == False{} : Bool}
  {M.rule(M.RSegment{List.append(&2, String, pre, p <> post)}, String.append(a, String.append(p, b))) == True{} : Bool}

# LAW model_name_segment_sound (R6): a name that passes segment_starts ps
# has a last part, after its last `/`, that begins with one of ps
# EXCLUDES: a hit in a part before the last `/` (qwen/llama), a hit inside
#   a segment
law model_name_segment_sound:
  for +ps: List<&2, String>
  for +s: String
  for h: {M.rule(M.RSegment{ps}, s) == True{} : Bool}
  exs pre: List<&2, String>
  exs p: String
  exs post: List<&2, String>
  exs a: String
  exs b: String
  {ps == List.append(&2, String, pre, p <> post) : List<&2, String>} & ({s == String.append(a, String.append(p, b)) : String} & ({sp_seg_start(a) == True{} : Bool} & {sp_has_slash(String.append(p, b)) == False{} : Bool}))

# Laws: the verdicts of sets over groups (R7)
# -------------------------------------------

# LAW model_name_holds_cell_complete (R7): one set over one group holds
# when one of its rules (rs = pre ++ [r] ++ post) holds for one of its
# names (g = gp ++ [s] ++ gq): the verdicts are exactly [True]
# EXCLUDES: a set that needs all its rules or all names, a rule or a name
#   past the first skipped
law model_name_holds_cell_complete:
  for +pre: List<&2, M.Rule>
  for +r: M.Rule
  for +post: List<&2, M.Rule>
  for +gp: List<&2, String>
  for +s: String
  for +gq: List<&2, String>
  for h: {M.rule(r, s) == True{} : Bool}
  {M.holds([List.append(&2, M.Rule, pre, r <> post)], [List.append(&2, String, gp, s <> gq)]) == [True{}] : List<&2, Bool>}

# LAW model_name_holds_cell_sound (R7): when the verdicts of one set rs over
# one group g are [True], some rule of rs holds for some name of g
# EXCLUDES: an empty set or group that holds, a set that holds with no
#   rule holding for any name
law model_name_holds_cell_sound:
  for +rs: List<&2, M.Rule>
  for +g: List<&2, String>
  for h: {M.holds([rs], [g]) == [True{}] : List<&2, Bool>}
  exs pre: List<&2, M.Rule>
  exs r: M.Rule
  exs post: List<&2, M.Rule>
  exs gp: List<&2, String>
  exs s: String
  exs gq: List<&2, String>
  {rs == List.append(&2, M.Rule, pre, r <> post) : List<&2, M.Rule>} & ({g == List.append(&2, String, gp, s <> gq) : List<&2, String>} & {M.rule(r, s) == True{} : Bool})

# LAW model_name_holds_count (R7): there is one verdict per group and set:
# as many verdicts as groups times sets
# EXCLUDES: a set or a group dropped or repeated, a verdict skipped when
#   False
law model_name_holds_count:
  for +sets: List<&2, List<&2, M.Rule>>
  for +groups: List<&2, List<&2, String>>
  {List.length(&2, Bool, M.holds(sets, groups)) == Nat.mul(List.length(&2, List<&2, String>, groups), List.length(&2, List<&2, M.Rule>, sets)) : Nat}

# LAW model_name_holds_groups_append (R7): the verdicts go group by group:
# those of the groups g1 ++ g2 are those of g1, then those of g2
# EXCLUDES: set-major order, groups reordered, one group's verdicts
#   depending on another group
law model_name_holds_groups_append:
  for +sets: List<&2, List<&2, M.Rule>>
  for +g1: List<&2, List<&2, String>>
  for +g2: List<&2, List<&2, String>>
  {M.holds(sets, List.append(&2, List<&2, String>, g1, g2)) == List.append(&2, Bool, M.holds(sets, g1), M.holds(sets, g2)) : List<&2, Bool>}

# LAW model_name_holds_sets_append (R7): within a group the verdicts go set
# by set: those of the sets s1 ++ s2 over one group are those of s1, then
# those of s2
# EXCLUDES: sets reordered within a group, one set's verdict depending on
#   another set
law model_name_holds_sets_append:
  for +s1: List<&2, List<&2, M.Rule>>
  for +s2: List<&2, List<&2, M.Rule>>
  for +g: List<&2, String>
  {M.holds(List.append(&2, List<&2, M.Rule>, s1, s2), [g]) == List.append(&2, Bool, M.holds(s1, [g]), M.holds(s2, [g])) : List<&2, Bool>}

# Laws: dash (R8)
# ---------------

# LAW model_name_dash_plain (R8): a text with no separator (sp_sep: Unicode
# White_Space from PropList.txt, `_`, `.`, `:`) is kept as it is
# EXCLUDES: a char that is no separator dashed or dropped, a non-ASCII
#   char changed
law model_name_dash_plain:
  for +s: String
  for h: {sp_no_sep(s) == True{} : Bool}
  {M.dash(s) == s : String}

# LAW model_name_dash_split (R8): for a text a, then a nonempty run of
# separators c ++ r, then a text b, where a does not end and b does not
# start with a separator (so the run is maximal), the text dashed is a
# dashed, then one `-`, then b dashed
# EXCLUDES: a run of separators turned into one `-` per char, a separator
#   kept, a White_Space char past ASCII (U+0085, U+3000) missed, a run at
#   the start or the end dropped, a `-` lost between runs
law model_name_dash_split:
  for +a: String
  for +c: Char
  for +r: String
  for +b: String
  for ha: {sp_ends_free(a) == True{} : Bool}
  for hr: {sp_all_sep(SCon{c, r}) == True{} : Bool}
  for hb: {sp_starts_free(b) == True{} : Bool}
  {M.dash(String.append(a, String.append(SCon{c, r}, b))) == String.append(M.dash(a), SCon{'-', M.dash(b)}) : String}

# LAW model_name_rule_example (R1-R6): anchor: the examples of the
# rulebook's rules (hits and misses)
# EXCLUDES: rules that drift from the regexes they replaced
law model_name_rule_example:
  {[M.rule(M.RNumber{["gpt-5."], 6n, True{}}, "gpt-5.6"), M.rule(M.RNumber{["gpt-5."], 6n, True{}}, "gpt-5.10.1"), M.rule(M.RNumber{["gpt-5."], 6n, True{}}, "gpt-5.010-x"), M.rule(M.RNumber{["gemini-"], 3n, False{}}, "gemini-2.5"), M.rule(M.RNumber{["gemini-"], 3n, False{}}, "gemini-25"), M.rule(M.RNumber{["gemini-", "gemini-live-"], 3n, False{}}, "gemini-live-3"), M.rule(M.RThen{"claude", "-4-"}, "claude-opus-4-6"), M.rule(M.RThen{"-4-", "claude"}, SCon{'x', SCon{'-', SCon{'4', SCon{'-', SCon{'\n', "claude"}}}}}), M.rule(M.RSegment{["qwen", "qwq"]}, "vendor/qwq-32b"), M.rule(M.RSegment{["qwen"]}, "qwen/llama"), M.rule(M.RIs{["gpt-5.4"]}, "gpt-5.45"), M.rule(M.RContains{["2.5-flash"]}, "x-2.5-flash-y")] == [True{}, False{}, True{}, False{}, True{}, True{}, True{}, False{}, True{}, False{}, False{}, True{}] : List<&2, Bool>}

# LAW model_name_dash_example (R8): anchor: a run of mixed separators, the
# ideographic space U+3000, a text with none
# EXCLUDES: a dash that drifts from the regex it replaced
law model_name_dash_example:
  {[M.dash("a 1.5:_b"), M.dash(SCon{'a', SCon{Chr{12288}, "b"}}), M.dash("ab")] == ["a-1-5-b", "a-b", "ab"] : List<&2, String>}

# Laws: the entry (R9)
# --------------------

# LAW model_name_entry_decides (R9): a request spelled by the grammar,
# every count, length and Nat within the wire, is answered with the
# spelling of the model's answer: the verdicts M.holds (pinned by R7's
# laws) or each text dashed by M.dash (pinned by R8's laws)
# EXCLUDES: a rule read as another, a field order other than Rust's, a set
#   or name lost or added, set-major verdicts, a reply spelled another way
law model_name_entry_decides:
  for +q: FM.Req
  for h: {sp_fit_req(q) == True{} : Bool}
  {FM.ffi(sp_w_req(q, "")) == sp_w_reply(q) : String}

# LAW model_name_entry_left_over (R9): input left over after a spelled
# request answers the error form
# EXCLUDES: trailing input ignored, or read as part of the request
law model_name_entry_left_over:
  for +q: FM.Req
  for +rest: String
  for h: {sp_fit_req(q) == True{} : Bool}
  for more: {String.is_empty(rest) == False{} : Bool}
  {FM.ffi(sp_w_req(q, rest)) == Wr.err("model_name: malformed request") : String}

# LAW model_name_entry_reads_only_requests (R9): an answer that is not the
# error form answers a request: the input is the spelling of a request that
# fits the wire, and the answer is the spelling of the model's answer to it
# (M.holds or M.dash, as in model_name_entry_decides)
# EXCLUDES: a decoder that accepts an unknown tag, a bad flag, a short
#   string, a count or a Nat past the wire or a missing field, and answers
#   it anyway
law model_name_entry_reads_only_requests:
  for +s: String
  for ok: {LawsBase.wire_opens_err(FM.ffi(s)) == False{} : Bool}
  exs q: FM.Req
  {(s, (sp_fit_req(q), FM.ffi(s))) == (sp_w_req(q, ""), (True{}, sp_w_reply(q))) : String & (Bool & String)}

# LAW model_name_entry_unknown_request (R9): a request tag past 1 is
# malformed, whatever follows
# EXCLUDES: an unknown request read as a known one (exact error bytes)
law model_name_entry_unknown_request:
  for +n: Nat
  for +rest: String
  {FM.ffi(Wr.put_nat(2n+n, rest)) == Wr.err("model_name: malformed request") : String}

# LAW model_name_entry_unknown_rule (R9): a rule tag past 5 (here the first
# rule of the first set) is malformed, whatever follows
# EXCLUDES: an unknown rule read as a known one (exact error bytes)
law model_name_entry_unknown_rule:
  for +m: Nat
  for +j: Nat
  for +n: Nat
  for +rest: String
  {FM.ffi(Wr.put_nat(0n, Wr.put_nat(1n+m, Wr.put_nat(1n+j, Wr.put_nat(6n+n, rest))))) == Wr.err("model_name: malformed request") : String}

# LAW model_name_entry_malformed_unless_request (R9): an input that does not
# begin with a spelled request that fits answers the malformed error: any
# other answer comes from an input that is a spelled request that fits,
# then possibly more
# EXCLUDES: another error text, or a reply, for input that holds no request
law model_name_entry_malformed_unless_request:
  for +s: String
  for other: {String.eq(FM.ffi(s), Wr.err("model_name: malformed request")) == False{} : Bool}
  exs q: FM.Req
  exs rest: String
  {(s, sp_fit_req(q)) == (sp_w_req(q, rest), True{}) : String & Bool}

# LAW model_name_entry_example (R9): anchor: the wire strings Rust sends and
# the replies it reads; no sets, an unknown request, an unknown rule, input
# left over
# EXCLUDES: a field order other than Rust's, another reply spelling
law model_name_entry_example:
  {[FM.ffi("1,1,3,a b"), FM.ffi("0,2,1,0,1,1,b1,3,1,a1,c1,1,3,abc"), FM.ffi("0,1,1,4,1,2,v.6,T1,1,3,v.7"), FM.ffi("0,0,0,"), FM.ffi("2,"), FM.ffi("0,1,1,6,"), FM.ffi("1,0,x")] == ["1,3,a-b", "2,TT", "1,T", "0,", Wr.err("model_name: malformed request"), Wr.err("model_name: malformed request"), Wr.err("model_name: malformed request")] : List<&2, String>}

# LAW model_name_entry_premises_witness (R9): a request that fits exists, and
# so does a malformed input
# EXCLUDES: a vacuous entry law whose premise no request meets
law model_name_entry_premises_witness:
  {(sp_fit_req(FM.QDash{["x"]}), FM.ffi("")) == (True{}, Wr.err("model_name: malformed request")) : Bool & String}
