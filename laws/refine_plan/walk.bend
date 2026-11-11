# eukhe: the laws of area refine_plan: the truncation scan and the fit of
# a refinement request (bend/refine_plan.bend; requirements R7 and R8 in
# ./model.bend)

import Base
import ../../bend/refine_plan.bend as Rp

# Spec helpers
# ------------

# Truncation (R7)
# ---------------
# A lexer, then counts: the candidate's chars outside its strings, and
# whether it ends inside one; cut off when it ends inside one or when more
# of those chars open a bracket than close one.

# where R7's scan is: outside a string, in one, right after a backslash
# in one
type RsMode is Data:
  RsOut{}
  RsStr{}
  RsEsc{}

def rs_lex.next(m: RsMode, bs: Bool, q: Bool) -> RsMode:
  match m:
    case RsOut{}:
      match q:
        case True{}:
          RsStr{}
        case False{}:
          RsOut{}
    case RsStr{}:
      match bs:
        case True{}:
          RsEsc{}
        case False{}:
          match q:
            case True{}:
              RsOut{}
            case False{}:
              RsStr{}
    case RsEsc{}:
      RsStr{}

# a char read outside a string that does not open one
def rs_lex.kept(m: RsMode, q: Bool) -> Bool:
  match m:
    case RsOut{}:
      Bool.not(q)
    case RsStr{}:
      False{}
    case RsEsc{}:
      False{}

def rs_lex.inside(m: RsMode) -> Bool:
  match m:
    case RsOut{}:
      False{}
    case RsStr{}:
      True{}
    case RsEsc{}:
      True{}

# a candidate's chars outside its strings, and whether it ends in one
type RsLex is Data:
  RsLex{out: String, open: Bool}

def rs_lex.keep(k: Bool, c: Char, l: RsLex) -> RsLex:
  match k:
    case True{}:
      match l:
        case RsLex{o, op}:
          RsLex{SCon{c, o}, op}
    case False{}:
      l

# R7's lexer: the chars outside strings (a `"` outside opens one; inside, a
# `\` escapes the next char and an unescaped `"` closes it)
def rs_lex(s: String, +m: RsMode) -> RsLex:
  match s:
    case SNil{}:
      RsLex{SNil{}, rs_lex.inside(m)}
    case SCon{+c, t}:
      +q = Char.is_eq(c, '"')
      rs_lex.keep(rs_lex.kept(m, q), c, rs_lex(t, rs_lex.next(m, Char.is_eq(c, '\\'), q)))

def rs_count.at(hit: Bool, r: Nat) -> Nat:
  match hit:
    case True{}:
      1n+r
    case False{}:
      r

# how many chars of s are a or b
def rs_count(s: String, +a: Char, +b: Char) -> Nat:
  match s:
    case SNil{}:
      0n
    case SCon{+c, t}:
      rs_count.at(Bool.or(Char.is_eq(c, a), Char.is_eq(c, b)), rs_count(t, a, b))

def rs_cut(l: RsLex) -> Bool:
  match l:
    case RsLex{+o, op}:
      Bool.or(op, Nat.is_gt(rs_count(o, '{', '['), rs_count(o, '}', ']')))

# R7: cut off when the candidate ends inside a string, or when more of its
# chars outside strings open a bracket than close one
def rs_incomplete(text: String) -> Bool:
  rs_cut(rs_lex(text, RsOut{}))

# Fit (R8)
# --------

# R8: the reserve: the system prompt's length plus 1024
def rs_reserve(sys: Nat) -> Nat:
  Nat.add(sys, 1024n)

# R8: a prompt plen long is within the budget (the window less the least
# of the max tokens, the output reserve and half the window, rounded
# down): the reserve plus the prompt plus that least is within the window,
# that is, plus any one of the three is
def rs_fits(w: Rp.Win, +plen: Nat) -> Bool:
  match w:
    case Rp.Win{+cw, mx, res, sys}:
      +x = Nat.add(rs_reserve(sys), plen)
      Bool.or(Nat.is_le(Nat.add(x, mx), cw), Bool.or(Nat.is_le(Nat.add(x, res), cw), Nat.is_le(Nat.add(x, Nat.div(cw, 2n)), cw)))

# R8: m is the middle of low and high, (low + high + 1) / 2 rounded down:
# twice m is low + high, or low + high + 1
def rs_mid(+lo: Nat, +hi: Nat, +m: Nat) -> Bool:
  Bool.or(Nat.is_eq(Nat.add(m, m), Nat.add(lo, hi)), Nat.is_eq(Nat.add(m, m), 1n+Nat.add(lo, hi)))

# R8: m is the max tokens a prompt plen long leaves: more than 0, at most
# the max tokens, m plus the reserve plus the prompt within the window, and
# m is the max tokens or fills the window (the least of the two)
def rs_room(w: Rp.Win, +plen: Nat, +m: Nat) -> Bool:
  match w:
    case Rp.Win{+cw, +mx, res, sys}:
      +x = Nat.add(rs_reserve(sys), plen)
      Bool.and(Nat.is_lt(0n, m), Bool.and(Nat.is_le(m, mx), Bool.and(Nat.is_le(Nat.add(x, m), cw), Bool.or(Nat.is_eq(m, mx), Nat.is_eq(Nat.add(x, m), cw)))))

# R8: a prompt plen long leaves no output tokens: the max tokens are 0, or
# the reserve plus the prompt fill the window
def rs_no_room(w: Rp.Win, +plen: Nat) -> Bool:
  match w:
    case Rp.Win{cw, mx, res, sys}:
      Bool.or(Nat.is_eq(mx, 0n), Nat.is_le(cw, Nat.add(rs_reserve(sys), plen)))

# Laws
# ----

# LAW refine_plan_incomplete_lex (R7): a candidate is cut off exactly when
# it ends inside a string, or when more of its chars outside strings (a
# `"` outside opens one; inside, a `\` escapes the next char and an
# unescaped `"` closes it) are `{` or `[` than `}` or `]`
# EXCLUDES: a bracket counted inside a string, an escaped quote closing a
#   string, extra closers read as open brackets, a closed candidate called
#   cut off
law refine_plan_incomplete_lex:
  for +text: String
  {Rp.incomplete(text) == rs_incomplete(text) : Bool}

# LAW refine_plan_fit_final_room (R8): the final prompt answers the max
# tokens m it leaves (rs_room: the least of the max tokens and what the
# window leaves, when more than 0), whatever the conversation
# EXCLUDES: max tokens past the window or past the max, a reserve other
#   than the system prompt plus 1024, room read from another length
law refine_plan_fit_final_room:
  for +w: Rp.Win
  for conv: Nat
  for +plen: Nat
  for +m: Nat
  for ok: {rs_room(w, plen, m) == True{} : Bool}
  {Rp.fit(w, conv, Rp.SFinal{}, plen) == Rp.TOk{m} : Rp.Step}

# LAW refine_plan_fit_final_no_room (R8): a final prompt that leaves no
# output tokens (rs_no_room) answers R8's refusal
# EXCLUDES: a zero answered as room, another refusal text
law refine_plan_fit_final_no_room:
  for +w: Rp.Win
  for conv: Nat
  for +plen: Nat
  for no: {rs_no_room(w, plen) == True{} : Bool}
  {Rp.fit(w, conv, Rp.SFinal{}, plen) == Rp.TNo{"Refinement prompt leaves no room for output in the model's context window; retry with a smaller request."} : Rp.Step}

# LAW refine_plan_fit_full_keeps (R8): a full prompt within the budget
# (rs_fits), or with an empty conversation, is the final one: it answers
# what the final prompt of its length answers
# EXCLUDES: a trim of a prompt that fits, a trim of an empty conversation
law refine_plan_fit_full_keeps:
  for +w: Rp.Win
  for +conv: Nat
  for +plen: Nat
  for keep: {Bool.or(rs_fits(w, plen), Nat.is_eq(conv, 0n)) == True{} : Bool}
  {Rp.fit(w, conv, Rp.SFull{}, plen) == Rp.fit(w, conv, Rp.SFinal{}, plen) : Rp.Step}

# LAW refine_plan_fit_full_trims (R8): a full prompt over the budget with
# a conversation starts the search over 0..the conversation's length: it
# asks for the middle m (rs_mid) of those bounds
# EXCLUDES: another budget or reserve, the middle rounded down, a search
#   over other bounds
law refine_plan_fit_full_trims:
  for +w: Rp.Win
  for +conv: Nat
  for +plen: Nat
  for +m: Nat
  for over: {rs_fits(w, plen) == False{} : Bool}
  for some: {Nat.is_eq(conv, 0n) == False{} : Bool}
  for mid: {rs_mid(0n, conv, m) == True{} : Bool}
  {Rp.fit(w, conv, Rp.SFull{}, plen) == Rp.TTry{m, Rp.SProbe{0n, conv, m}} : Rp.Step}

# LAW refine_plan_fit_probe_up (R8): a probed length len whose prompt is
# within the budget raises the low bound to len; while it is below the
# high bound the search asks for the middle m of len and high
# EXCLUDES: a bound moved the wrong way, the middle rounded down, a probe
#   past the bounds
law refine_plan_fit_probe_up:
  for +w: Rp.Win
  for conv: Nat
  for lo: Nat
  for +hi: Nat
  for +len: Nat
  for +plen: Nat
  for +m: Nat
  for fits: {rs_fits(w, plen) == True{} : Bool}
  for more: {Nat.is_lt(len, hi) == True{} : Bool}
  for mid: {rs_mid(len, hi, m) == True{} : Bool}
  {Rp.fit(w, conv, Rp.SProbe{lo, hi, len}, plen) == Rp.TTry{m, Rp.SProbe{len, hi, m}} : Rp.Step}

# LAW refine_plan_fit_probe_up_last (R8): a probed length len whose prompt
# is within the budget, with no room above it, is the final length
# EXCLUDES: a search that goes on past its bounds, a final length other
#   than the low bound
law refine_plan_fit_probe_up_last:
  for +w: Rp.Win
  for conv: Nat
  for lo: Nat
  for +hi: Nat
  for +len: Nat
  for +plen: Nat
  for fits: {rs_fits(w, plen) == True{} : Bool}
  for last: {Nat.is_lt(len, hi) == False{} : Bool}
  {Rp.fit(w, conv, Rp.SProbe{lo, hi, len}, plen) == Rp.TTry{len, Rp.SFinal{}} : Rp.Step}

# LAW refine_plan_fit_probe_down (R8): a probed length len whose prompt is
# over the budget lowers the high bound to len less one; while the low
# bound is below it the search asks for the middle m of low and len less
# one
# EXCLUDES: a bound moved the wrong way or by another step, the middle
#   rounded down
law refine_plan_fit_probe_down:
  for +w: Rp.Win
  for conv: Nat
  for +lo: Nat
  for hi: Nat
  for +len: Nat
  for +plen: Nat
  for +m: Nat
  for over: {rs_fits(w, plen) == False{} : Bool}
  for more: {Nat.is_lt(lo, Nat.sub(len, 1n)) == True{} : Bool}
  for mid: {rs_mid(lo, Nat.sub(len, 1n), m) == True{} : Bool}
  {Rp.fit(w, conv, Rp.SProbe{lo, hi, len}, plen) == Rp.TTry{m, Rp.SProbe{lo, Nat.sub(len, 1n), m}} : Rp.Step}

# LAW refine_plan_fit_probe_down_last (R8): a probed length len whose
# prompt is over the budget, with the low bound no longer below len less
# one, makes the low bound the final length
# EXCLUDES: a final length other than the low bound, a search that goes on
#   past its bounds
law refine_plan_fit_probe_down_last:
  for +w: Rp.Win
  for conv: Nat
  for +lo: Nat
  for hi: Nat
  for +len: Nat
  for +plen: Nat
  for over: {rs_fits(w, plen) == False{} : Bool}
  for last: {Nat.is_lt(lo, Nat.sub(len, 1n)) == False{} : Bool}
  {Rp.fit(w, conv, Rp.SProbe{lo, hi, len}, plen) == Rp.TTry{lo, Rp.SFinal{}} : Rp.Step}
