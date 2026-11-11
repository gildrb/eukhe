# eukhe: the laws of area slash_args: the model (bend/slash_args.bend)

import Base
import ../../bend/slash_args.bend as Sa

# (D1) The arguments of `/goal` and `/autonomous`, the words of a command
# ------------------------------------------------------------------------
# bend/slash_args.bend, run as the compiled core by bend/ffi_slash_args.bend
# (eukhe-bend rules/slash_args.rs; asked by eukhe-core slash_command_args.rs
# for `/goal` and `/autonomous`, goals.rs for a goal objective, and the
# prompt templates for a command's words). Every input is free: any text.
#
# R1: whitespace is Unicode White_Space (Rust `char::is_whitespace`:
#     sa_white); trimming drops it at both ends. A keyword
#     compares with the text's ASCII letters lowercased (Rust
#     `to_lowercase`: no other char lowercases to a letter of a keyword).
# R2: the words of a text (Rust `parse_command_args`): read char by char;
#     outside a quote, `"` or `'` opens a quote that only the same char
#     closes (the quote chars are dropped, the chars between kept), and
#     whitespace ends a word that has chars or held a quote; a word that
#     held a quote is kept even when empty; at the end the last such word.
# R3: `/goal <args>`: the args trimmed, lowercased: empty or `status` is
#     the status; `clear` or `stop` clears; `pause`; `resume`.
# R4: else the first piece (up to the first whitespace char) `--budget` or
#     `--token-budget`: the value is the next piece after the whitespace
#     that follows, the objective the text after the one whitespace char
#     that ends the value (no such char: `Usage: /goal [--budget <tokens>]
#     <objective>`); `--budget=N` / `--token-budget=N` (a piece that starts
#     so): N after the piece's first `=`, the objective the text after the
#     piece. N must be digits without a leading 0 that a u64 holds (at most
#     20 digits, 20 only up to 18446744073709551615), else `Goal token
#     budget must be a positive integer.`; any other first piece: no
#     budget, the objective is the whole args.
# R5: the objective, trimmed: empty answers `Goal objective must not be
#     empty.`, more than 4000 chars `Goal objective must be at most 4000
#     characters.`, else the goal starts with it (and its budget digits).
#     A goal objective alone (the objective question) is judged so,
#     without a budget.
# R6: `/autonomous <args>`, over the words of R2: none, or a first word
#     `status` alone, is the status (`status` with more:
#     `Unexpected autonomous argument: <second word>. <usage>`); `on`,
#     `enable`, `enabled` reads the options of the words after it; `off`,
#     `disable`, `disabled` alone is off (with more: the unexpected error);
#     anything else answers the usage text alone.
# R7: options, read in order: a word that does not start with `--`
#     answers `Unexpected autonomous argument: <word>. <usage>`. The flag
#     is the word before its first `=`; its name the flag without
#     `--autonomous-` when it starts so, else without `--`. A name that is
#     none of max-continuations, max-turns, max-tokens, timeout-ms, gate,
#     gate-retries, gate-timeout-ms, subagent-keep-alive-ms answers
#     `Unknown autonomous budget flag: <flag>. <usage>`. The value: after
#     the first `=` when the word holds one, else the next word when there
#     is one that does not start with `--` (it is then consumed); none, or
#     an empty one, answers `Missing value for <flag>. <usage>`.
# R8: a limit (the first four) is `unlimited` (its ASCII letters
#     lowercased) or, with every `,` and `_` dropped, R4's u64 digits; else
#     `--<name> must be a positive integer or "unlimited". <usage>`. Gate
#     retries and timeout: R4's u64 digits after the same drop, else
#     `--<name> must be a positive integer. <usage>`. The keep-alive: after
#     the drop, `0` or positive digits up to 2147483647, else
#     `--subagent-keep-alive-ms must be 0 or a positive integer up to
#     2147483647. <usage>`. `--gate` adds its value to the gate commands.
# R9: the first bad word (in order) answers its error; a value named
#     again overrides the earlier one; the gate commands keep their order.
#     The answer: when any of the four limits is named, every limit not
#     named is unlimited; the gates are named when a command, a retry or a
#     timeout was (the commands only when there is one).
#
# <usage> is the text sa_usage() (Eukhe's own: no Rust constant holds it;
# Rust only checks that the error starts with `Usage: /autonomous
# [status|off]`, crates/eukhe-core/src/slash_command_args.rs:208).
# Changed from the Rust it replaced: after `--budget N`, a value ended by a
# multi-byte whitespace char (U+3000, U+00A0, ...) made the Rust slice
# inside that char and panic; the objective is now the text after it.

# Terms
# -----

def sa_in(+x: U32, xs: List<&2, U32>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case y <> rest:
      Bool.or(U32.is_eq(x, y), sa_in(x, rest))

# R1: Unicode White_Space (Unicode PropList.txt; Rust `char::is_whitespace`),
# by code point
def sa_ws() -> List<&2, U32>:
  [9, 10, 11, 12, 13, 32, 133, 160, 5760, 8192, 8193, 8194, 8195, 8196, 8197, 8198, 8199, 8200, 8201, 8202, 8232, 8233, 8239, 8287, 12288]

def sa_white(c: Char) -> Bool:
  sa_in(Char.to_u32(c), sa_ws())

# R1: a text of White_Space only (the empty text too)
def sa_blank(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(sa_white(c), sa_blank(t))

# R1: a text without White_Space
def sa_solid(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Bool.not(sa_white(c)), sa_solid(t))

# R1: the last of c then t is not White_Space
def sa_last_dark(t: String, c: Char) -> Bool:
  match t:
    case SNil{}:
      Bool.not(sa_white(c))
    case SCon{d, u}:
      sa_last_dark(u, d)

# R1: s starts and ends with a char that is not White_Space (s is its own
# trim, and not empty)
def sa_edge(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, t}:
      Bool.and(Bool.not(sa_white(c)), sa_last_dark(t, c))

# R2: a quote char
def sa_qc(+c: Char) -> Bool:
  Bool.or(Char.is_eq(c, '"'), Char.is_eq(c, '\''))

def sa_step.out(b: Bool, c: Char) -> Maybe<&2, Char>:
  match b:
    case True{}:
      Some{c}
    case False{}:
      None{}

def sa_step.in(b: Bool, x: Char) -> Maybe<&2, Char>:
  match b:
    case True{}:
      None{}
    case False{}:
      Some{x}

# R2: the quote open after the char c, q the one open before it (none:
# outside a quote): outside, a quote char opens one; inside, only the
# same char closes it
def sa_step(+c: Char, q: Maybe<&2, Char>) -> Maybe<&2, Char>:
  match q:
    case None{}:
      sa_step.out(sa_qc(c), c)
    case Some{+x}:
      sa_step.in(Char.is_eq(c, x), x)

# R2: the quote open after the text s, q the one open before it
def sa_end(s: String, q: Maybe<&2, Char>) -> Maybe<&2, Char>:
  match s:
    case SNil{}:
      q
    case SCon{+c, t}:
      sa_end(t, sa_step(c, q))

def sa_none(m: Maybe<&2, Char>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{x}:
      False{}

# R2: no quote is open after s
def sa_closed(s: String) -> Bool:
  sa_none(sa_end(s, None{}))

# R2: c opens or closes a quote, q the one open before it
def sa_mark(+c: Char, q: Maybe<&2, Char>) -> Bool:
  match q:
    case None{}:
      sa_qc(c)
    case Some{x}:
      Char.is_eq(c, x)

def sa_unquote.at(b: Bool, c: Char, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, r}

# R2: the chars of s that open or close no quote, q open before s
def sa_unquote(s: String, +q: Maybe<&2, Char>) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      sa_unquote.at(sa_mark(c, q), c, sa_unquote(t, sa_step(c, q)))

def sa_tight.at(q: Maybe<&2, Char>, c: Char) -> Bool:
  match q:
    case None{}:
      Bool.not(sa_white(c))
    case Some{x}:
      True{}

# R2: s holds no White_Space outside a quote, q open before s
def sa_tight(s: String, +q: Maybe<&2, Char>) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{+c, t}:
      Bool.and(sa_tight.at(q, c), sa_tight(t, sa_step(c, q)))

# R4: the budget flag k names: `--budget` (True) or `--token-budget`
def sa_flag(k: Bool) -> String:
  match k:
    case True{}:
      "--budget"
    case False{}:
      "--token-budget"

def sa_verdict.at(ok: Bool, o: String, b: Maybe<&2, String>) -> Sa.Goal:
  match ok:
    case True{}:
      Sa.GStart{o, b}
    case False{}:
      Sa.GErr{"Goal objective must be at most 4000 characters."}

# R5: the goal of a trimmed, non-empty objective o with the budget b: it
# starts when o has at most 4000 chars
def sa_verdict(+o: String, b: Maybe<&2, String>) -> Sa.Goal:
  sa_verdict.at(Nat.is_le(String.length(o), 4000n), o, b)

def sa_budget.at(ok: Bool, v: String, +o: String) -> Sa.Goal:
  match ok:
    case True{}:
      sa_verdict(o, Some{v})
    case False{}:
      Sa.GErr{"Goal token budget must be a positive integer."}

# R4: the goal of the budget digits v before the objective o: v must be
# R4's u64 digits (Sa.u64, pinned by slash_args_u64_example)
def sa_budget(+v: String, +o: String) -> Sa.Goal:
  sa_budget.at(Sa.u64(v), v, o)

# R4, R5: the goal of a budget flag with the digits v and no objective
def sa_budget_none(ok: Bool) -> Sa.Goal:
  match ok:
    case True{}:
      Sa.GErr{"Goal objective must not be empty."}
    case False{}:
      Sa.GErr{"Goal token budget must be a positive integer."}

# R3: a keyword of `/goal` (lowercased)
def sa_keyword(+l: String) -> Bool:
  Bool.or(String.eq(l, "status"), Bool.or(String.eq(l, "clear"), Bool.or(String.eq(l, "stop"), Bool.or(String.eq(l, "pause"), String.eq(l, "resume")))))

def sa_piece.at(w: Bool, c: Char, r: String) -> String:
  match w:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, r}

# R4: the first piece of s: its chars before its first White_Space
def sa_piece(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      sa_piece.at(sa_white(c), c, sa_piece(t))

# R4: a first piece that asks for a budget
def sa_asks(+p: String) -> Bool:
  Bool.or(String.eq(p, "--budget"), Bool.or(String.eq(p, "--token-budget"), Bool.or(String.starts_with(p, "--budget="), String.starts_with(p, "--token-budget="))))

# R6: the usage text of `/autonomous`
def sa_usage() -> String:
  "Usage: /autonomous [status|off] or /autonomous on [--max-continuations <n|unlimited>] [--max-turns <n|unlimited>] [--max-tokens <n|unlimited>] [--timeout-ms <n|unlimited>] [--gate <command>] [--gate-retries <n>] [--gate-timeout-ms <n>] [--subagent-keep-alive-ms <n>]"

# R6, R7: `<head><w>. <usage>`
def sa_err(+head: String, w: String) -> String:
  String.concat([head, w, ". ", sa_usage()])

# R6: the first word's kinds (lowercased)
def sa_on(+l: String) -> Bool:
  Bool.or(String.eq(l, "on"), Bool.or(String.eq(l, "enable"), String.eq(l, "enabled")))

def sa_off(+l: String) -> Bool:
  Bool.or(String.eq(l, "off"), Bool.or(String.eq(l, "disable"), String.eq(l, "disabled")))

# R7: the flag names
def sa_known(+n: String) -> Bool:
  Bool.or(String.eq(n, "max-continuations"), Bool.or(String.eq(n, "max-turns"), Bool.or(String.eq(n, "max-tokens"), Bool.or(String.eq(n, "timeout-ms"), Bool.or(String.eq(n, "gate"), Bool.or(String.eq(n, "gate-retries"), Bool.or(String.eq(n, "gate-timeout-ms"), String.eq(n, "subagent-keep-alive-ms"))))))))

def sa_raw.at(e: Bool, c: Char, r: String) -> String:
  match e:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, r}

# R7: a flag word's flag: its text before its first `=`
def sa_raw(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      sa_raw.at(Char.is_eq(c, '='), c, sa_raw(t))

def sa_name.at(a: Bool, d: Bool, +f: String) -> String:
  match a:
    case True{}:
      String.drop(f, 13n)
    case False{}:
      match d:
        case True{}:
          String.drop(f, 2n)
        case False{}:
          f

# R7: a flag's name: without `--autonomous-` when it starts so, else
# without `--`
def sa_name(+f: String) -> String:
  sa_name.at(String.starts_with(f, "--autonomous-"), String.starts_with(f, "--"), f)

# R6: the answer to one word, lowercased l
def sa_alone.at(st: Bool, on: Bool, off: Bool) -> Sa.Auto:
  match st:
    case True{}:
      Sa.AStatus{}
    case False{}:
      match on:
        case True{}:
          Sa.AOn{Sa.Conf{None{}, None{}, None{}, None{}, None{}, None{}}}
        case False{}:
          match off:
            case True{}:
              Sa.AOff{}
            case False{}:
              Sa.AErr{sa_usage()}

def sa_alone(+l: String) -> Sa.Auto:
  sa_alone.at(String.eq(l, "status"), sa_on(l), sa_off(l))

# R7: the text after the first `=` of s (empty without one)
def sa_after.at(e: Bool, t: String, r: String) -> String:
  match e:
    case True{}:
      t
    case False{}:
      r

def sa_after(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      sa_after.at(Char.is_eq(c, '='), t, sa_after(t))

def sa_value.next(f: Bool, v: String) -> Maybe<&2, String>:
  match f:
    case True{}:
      None{}
    case False{}:
      Some{v}

def sa_value.at(e: Bool, x: String, t: List<&2, String>) -> Maybe<&2, String>:
  match e:
    case True{}:
      Some{sa_after(x)}
    case False{}:
      match t:
        case Nil{}:
          None{}
        case +v <> u:
          sa_value.next(String.starts_with(v, "--"), v)

# R7: the value of the option word x before the words t: after x's first
# `=` when x holds one; else the next word, when there is one that does not
# start with `--`; else none
def sa_value(+x: String, t: List<&2, String>) -> Maybe<&2, String>:
  sa_value.at(String.contains(x, "="), x, t)

# R7: a value is given: there is one and it is not empty
def sa_given(m: Maybe<&2, String>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{v}:
      Bool.not(String.is_empty(v))

# R7: the flag prefix: `--autonomous-` (True) or `--`
def sa_prefix(p: Bool) -> String:
  match p:
    case True{}:
      "--autonomous-"
    case False{}:
      "--"

# R7: the flag names, in R7's order
def sa_flag_name(k: Nat) -> String:
  match k:
    case 0n:
      "max-continuations"
    case 1n:
      "max-turns"
    case 2n:
      "max-tokens"
    case 3n:
      "timeout-ms"
    case 4n:
      "gate"
    case 5n:
      "gate-retries"
    case 6n:
      "gate-timeout-ms"
    case 7n+u:
      "subagent-keep-alive-ms"

def sa_ungroup.at(b: Bool, c: Char, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, r}

# R8: s without its `,` and `_` chars
def sa_ungroup(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      sa_ungroup.at(Bool.or(Char.is_eq(c, ','), Char.is_eq(c, '_')), c, sa_ungroup(t))

# R9: the options with the limit k at l: once a limit is named, the other
# limits are unlimited; no gate, no keep-alive
def sa_lim_conf(k: Nat, l: Sa.Lim) -> Sa.Conf:
  match k:
    case 0n:
      Sa.Conf{Some{l}, Some{Sa.LUnl{}}, Some{Sa.LUnl{}}, Some{Sa.LUnl{}}, None{}, None{}}
    case 1n:
      Sa.Conf{Some{Sa.LUnl{}}, Some{l}, Some{Sa.LUnl{}}, Some{Sa.LUnl{}}, None{}, None{}}
    case 2n:
      Sa.Conf{Some{Sa.LUnl{}}, Some{Sa.LUnl{}}, Some{l}, Some{Sa.LUnl{}}, None{}, None{}}
    case 3n+u:
      Sa.Conf{Some{Sa.LUnl{}}, Some{Sa.LUnl{}}, Some{Sa.LUnl{}}, Some{l}, None{}, None{}}

def sa_option.lim(k: Nat, +n: String, unl: Bool, num: Bool, d: String) -> Sa.Auto:
  match unl:
    case True{}:
      Sa.AOn{sa_lim_conf(k, Sa.LUnl{})}
    case False{}:
      match num:
        case True{}:
          Sa.AOn{sa_lim_conf(k, Sa.LNum{d})}
        case False{}:
          Sa.AErr{String.concat(["--", n, " must be a positive integer or \"unlimited\". ", sa_usage()])}

def sa_option.num(ok: Bool, +n: String, c: Sa.Conf) -> Sa.Auto:
  match ok:
    case True{}:
      Sa.AOn{c}
    case False{}:
      Sa.AErr{String.concat(["--", n, " must be a positive integer. ", sa_usage()])}

def sa_option.keep(ok: Bool, d: String) -> Sa.Auto:
  match ok:
    case True{}:
      Sa.AOn{Sa.Conf{None{}, None{}, None{}, None{}, None{}, Some{d}}}
    case False{}:
      Sa.AErr{String.concat(["--subagent-keep-alive-ms must be 0 or a positive integer up to 2147483647. ", sa_usage()])}

# R8, R9: `/autonomous on` with the one option of flag k and the non-empty
# value v: a limit is `unlimited` (lowercased) or R4's u64 digits after
# R8's drop (Sa.u64, pinned by slash_args_u64_example), else its error;
# `--gate` names the one command v; gate retries and timeout are such
# digits, else their error; the keep-alive is 0 or positive digits up to
# 2147483647 (Sa.keep_ok, pinned by slash_args_u64_example), else its error
def sa_option(k: Nat, +v: String) -> Sa.Auto:
  match k:
    case 0n:
      sa_option.lim(0n, "max-continuations", String.eq(String.to_lower(v), "unlimited"), Sa.u64(sa_ungroup(v)), sa_ungroup(v))
    case 1n:
      sa_option.lim(1n, "max-turns", String.eq(String.to_lower(v), "unlimited"), Sa.u64(sa_ungroup(v)), sa_ungroup(v))
    case 2n:
      sa_option.lim(2n, "max-tokens", String.eq(String.to_lower(v), "unlimited"), Sa.u64(sa_ungroup(v)), sa_ungroup(v))
    case 3n:
      sa_option.lim(3n, "timeout-ms", String.eq(String.to_lower(v), "unlimited"), Sa.u64(sa_ungroup(v)), sa_ungroup(v))
    case 4n:
      Sa.AOn{Sa.Conf{None{}, None{}, None{}, None{}, Some{Sa.Gates{Some{[v]}, None{}, None{}}}, None{}}}
    case 5n:
      sa_option.num(Sa.u64(sa_ungroup(v)), "gate-retries", Sa.Conf{None{}, None{}, None{}, None{}, Some{Sa.Gates{None{}, Some{sa_ungroup(v)}, None{}}}, None{}})
    case 6n:
      sa_option.num(Sa.u64(sa_ungroup(v)), "gate-timeout-ms", Sa.Conf{None{}, None{}, None{}, None{}, Some{Sa.Gates{None{}, None{}, Some{sa_ungroup(v)}}}, None{}})
    case 7n+u:
      sa_option.keep(Sa.keep_ok(sa_ungroup(v)), sa_ungroup(v))

# R7: a value missing answers its error; else R8
def sa_option_or_missing(k: Nat, +raw: String, v: String) -> Sa.Auto:
  match v:
    case SNil{}:
      Sa.AErr{sa_err("Missing value for ", raw)}
    case SCon{c, t}:
      sa_option(k, SCon{c, t})

# Laws: the words (R1, R2)
# ------------------------

# LAW slash_args_words_split (R1, R2): for every text s after which no
# quote is open, every White_Space char c and every text t, the words of
# s, c, t are the words of s, then the words of t
# EXCLUDES: ASCII-only whitespace, a word that runs across the White_Space
#   char, a word dropped or duplicated at the split, words reordered
law slash_args_words_split:
  for +s: String
  for cl: {sa_closed(s) == True{} : Bool}
  for +c: Char
  for cw: {sa_white(c) == True{} : Bool}
  for +t: String
  {Sa.words(String.append(s, SCon{c, t})) == List.append(&2, String, Sa.words(s), Sa.words(t)) : List<&2, String>}

# LAW slash_args_words_one (R2): for every non-empty text with no
# White_Space outside a quote, its words are one word: its chars that open
# or close no quote (a quote opened by `"` or `'` closes only at the same
# char; one left open runs to the end)
# EXCLUDES: quote chars kept, a quote closed by the other quote char, an
#   empty quoted word (`""`) dropped, White_Space inside a quote splitting
#   the word, a word split at a quote
law slash_args_words_one:
  for +c: Char
  for +t: String
  for ti: {sa_tight(SCon{c, t}, None{}) == True{} : Bool}
  {Sa.words(SCon{c, t}) == [sa_unquote(SCon{c, t}, None{})] : List<&2, String>}

# Laws: `/goal` (R1, R3-R5)
# -------------------------

# LAW slash_args_goal_padding (R1, R3): for every text s and every two
# White_Space texts w1 and w2, `/goal` asks of s between them what it asks
# of s
# EXCLUDES: untrimmed args, ASCII-only trimming, whitespace read into a
#   keyword, a flag or the objective
law slash_args_goal_padding:
  for +w1: String
  for b1: {sa_blank(w1) == True{} : Bool}
  for +s: String
  for +w2: String
  for b2: {sa_blank(w2) == True{} : Bool}
  {Sa.goal(String.append(w1, String.append(s, w2))) == Sa.goal(s) : Sa.Goal}

# LAW slash_args_goal_blank (R3): every White_Space text (the empty one
# too) asks for the status
# EXCLUDES: blank args starting a goal or answering an error
law slash_args_goal_blank:
  for +w: String
  for b: {sa_blank(w) == True{} : Bool}
  {Sa.goal(w) == Sa.GStatus{} : Sa.Goal}

# LAW slash_args_goal_status (R3): every trimmed text whose lowercase is
# `status` asks for the status
# EXCLUDES: a case-sensitive keyword
law slash_args_goal_status:
  for +t: String
  for e: {sa_edge(t) == True{} : Bool}
  for k: {String.eq(String.to_lower(t), "status") == True{} : Bool}
  {Sa.goal(t) == Sa.GStatus{} : Sa.Goal}

# LAW slash_args_goal_clear (R3): every trimmed text whose lowercase is
# `clear` or `stop` clears the goal
# EXCLUDES: `stop` not clearing, a case-sensitive keyword
law slash_args_goal_clear:
  for +t: String
  for e: {sa_edge(t) == True{} : Bool}
  for k: {Bool.or(String.eq(String.to_lower(t), "clear"), String.eq(String.to_lower(t), "stop")) == True{} : Bool}
  {Sa.goal(t) == Sa.GClear{} : Sa.Goal}

# LAW slash_args_goal_pause (R3): every trimmed text whose lowercase is
# `pause` pauses the goal
# EXCLUDES: a case-sensitive keyword
law slash_args_goal_pause:
  for +t: String
  for e: {sa_edge(t) == True{} : Bool}
  for k: {String.eq(String.to_lower(t), "pause") == True{} : Bool}
  {Sa.goal(t) == Sa.GPause{} : Sa.Goal}

# LAW slash_args_goal_resume (R3): every trimmed text whose lowercase is
# `resume` resumes the goal
# EXCLUDES: a case-sensitive keyword
law slash_args_goal_resume:
  for +t: String
  for e: {sa_edge(t) == True{} : Bool}
  for k: {String.eq(String.to_lower(t), "resume") == True{} : Bool}
  {Sa.goal(t) == Sa.GResume{} : Sa.Goal}

# LAW slash_args_goal_objective (R3-R5): every trimmed text that is no
# keyword (lowercased) and whose first piece asks for no budget starts the
# goal with all of it as the objective and no budget, when it has at most
# 4000 chars (else the too-long error)
# EXCLUDES: an objective cut at its first word, a keyword read inside an
#   objective, an objective over 4000 chars started, a limit off by one
law slash_args_goal_objective:
  for +t: String
  for +e: {sa_edge(t) == True{} : Bool}
  for k: {sa_keyword(String.to_lower(t)) == False{} : Bool}
  for f: {sa_asks(sa_piece(t)) == False{} : Bool}
  {Sa.goal(t) == sa_verdict(t, None{}) : Sa.Goal}

# LAW slash_args_goal_budget_eq (R4, R5): for both budget flags F, every
# text v without White_Space, every White_Space char c, every White_Space
# text w and every trimmed objective o: `F=v`, then c, w and o, asks for
# o with the budget v when v is R4's digits (else the bad-budget error);
# `F=v` alone asks for no objective (the empty-objective error) or answers
# the bad-budget error
# EXCLUDES: the value taken after a later `=`, the separator kept in the
#   objective, a bad budget accepted, the empty objective started
law slash_args_goal_budget_eq:
  for +k: Bool
  for +v: String
  for +vs: {sa_solid(v) == True{} : Bool}
  for +c: Char
  for +cw: {sa_white(c) == True{} : Bool}
  for +w: String
  for +wb: {sa_blank(w) == True{} : Bool}
  for +o: String
  for +oe: {sa_edge(o) == True{} : Bool}
  {Sa.goal(String.append(sa_flag(k), SCon{'=', String.append(v, SCon{c, String.append(w, o)})})) == sa_budget(v, o) : Sa.Goal} &
  {Sa.goal(String.append(sa_flag(k), SCon{'=', v})) == sa_budget_none(Sa.u64(v)) : Sa.Goal}

# LAW slash_args_goal_budget_spaced (R4, R5): for both budget flags F,
# every two White_Space chars c and d, every two White_Space texts w and x,
# every non-empty text v without White_Space and every trimmed objective
# o: F, c, w, v, d, x, o asks for o with the budget v when v is R4's
# digits (else the bad-budget error); F alone, or F then c, w and v, is
# the usage error
# EXCLUDES: a multi-byte whitespace char after the value mishandled, the
#   value read into the objective, the usage error lost, a bad budget
#   accepted
law slash_args_goal_budget_spaced:
  for +k: Bool
  for +c: Char
  for +cw: {sa_white(c) == True{} : Bool}
  for +w: String
  for +wb: {sa_blank(w) == True{} : Bool}
  for +v0: Char
  for +vs: String
  for +vd: {sa_solid(SCon{v0, vs}) == True{} : Bool}
  for +d: Char
  for +dw: {sa_white(d) == True{} : Bool}
  for +x: String
  for +xb: {sa_blank(x) == True{} : Bool}
  for +o: String
  for +oe: {sa_edge(o) == True{} : Bool}
  {Sa.goal(String.append(sa_flag(k), SCon{c, String.append(w, String.append(SCon{v0, vs}, SCon{d, String.append(x, o)}))})) == sa_budget(SCon{v0, vs}, o) : Sa.Goal} &
  {Sa.goal(sa_flag(k)) == Sa.GErr{"Usage: /goal [--budget <tokens>] <objective>"} : Sa.Goal} &
  {Sa.goal(String.append(sa_flag(k), SCon{c, String.append(w, SCon{v0, vs})})) == Sa.GErr{"Usage: /goal [--budget <tokens>] <objective>"} : Sa.Goal}

# LAW slash_args_objective_judged (R5): for every two White_Space texts w1
# and w2, every trimmed objective o and every budget b, the objective o
# between them is judged as o (R5); a White_Space objective is the
# empty-objective error
# EXCLUDES: an untrimmed objective, ASCII-only trimming, a blank objective
#   started, the 4000-char limit off by one
law slash_args_objective_judged:
  for +w1: String
  for +b1: {sa_blank(w1) == True{} : Bool}
  for +o: String
  for +oe: {sa_edge(o) == True{} : Bool}
  for +w2: String
  for b2: {sa_blank(w2) == True{} : Bool}
  for +b: Maybe<&2, String>
  {Sa.goal.objective(String.append(w1, String.append(o, w2)), b) == sa_verdict(o, b) : Sa.Goal} &
  {Sa.goal.objective(w1, b) == Sa.GErr{"Goal objective must not be empty."} : Sa.Goal}

# Laws: `/autonomous` (R6, R7)
# ----------------------------

# LAW slash_args_auto_none (R6): a text of no words asks for the status
# EXCLUDES: blank args read as an error
law slash_args_auto_none:
  for +s: String
  for ws: {Sa.words(s) == [] : List<&2, String>}
  {Sa.auto(s) == Sa.AStatus{} : Sa.Auto}

# LAW slash_args_auto_alone (R6): a text of one word w asks, by w
# lowercased: `status` the status; `on`, `enable`, `enabled` autonomous
# mode with no option named; `off`, `disable`, `disabled` off; anything
# else answers the usage text
# EXCLUDES: a case-sensitive keyword, a keyword of one kind read as
#   another, an unknown word accepted
law slash_args_auto_alone:
  for +s: String
  for +w: String
  for ws: {Sa.words(s) == [w] : List<&2, String>}
  {Sa.auto(s) == sa_alone(String.to_lower(w)) : Sa.Auto}

# LAW slash_args_auto_more (R6): a text whose first word is `status`,
# `off`, `disable` or `disabled` (lowercased) and has a second word v
# answers `Unexpected autonomous argument: <v>. <usage>`
# EXCLUDES: words after `status`/`off` ignored, another word named
law slash_args_auto_more:
  for +s: String
  for +w: String
  for +v: String
  for +t: List<&2, String>
  for ws: {Sa.words(s) == w <> v <> t : List<&2, String>}
  for k: {Bool.or(String.eq(String.to_lower(w), "status"), sa_off(String.to_lower(w))) == True{} : Bool}
  {Sa.auto(s) == Sa.AErr{sa_err("Unexpected autonomous argument: ", v)} : Sa.Auto}

# LAW slash_args_auto_other (R6): a text whose first word (lowercased) is
# no keyword answers the usage text alone, whatever follows
# EXCLUDES: an unknown first word read as on, off or the status
law slash_args_auto_other:
  for +s: String
  for +w: String
  for +t: List<&2, String>
  for ws: {Sa.words(s) == w <> t : List<&2, String>}
  for k: {Bool.or(String.eq(String.to_lower(w), "status"), Bool.or(sa_on(String.to_lower(w)), sa_off(String.to_lower(w)))) == False{} : Bool}
  {Sa.auto(s) == Sa.AErr{sa_usage()} : Sa.Auto}

# LAW slash_args_auto_unexpected (R7): after `on`, `enable` or `enabled`
# (lowercased), a first option word x that does not start with `--`
# answers `Unexpected autonomous argument: <x>. <usage>`, whatever follows
# EXCLUDES: a stray word ignored or read as a value, a later error
#   reported before it
law slash_args_auto_unexpected:
  for +s: String
  for +w: String
  for +x: String
  for +t: List<&2, String>
  for ws: {Sa.words(s) == w <> x <> t : List<&2, String>}
  for k: {sa_on(String.to_lower(w)) == True{} : Bool}
  for d: {String.starts_with(x, "--") == False{} : Bool}
  {Sa.auto(s) == Sa.AErr{sa_err("Unexpected autonomous argument: ", x)} : Sa.Auto}

# LAW slash_args_auto_unknown (R7): after `on`, `enable` or `enabled`
# (lowercased), a first option word x that starts with `--` and whose
# flag (before its first `=`) names no budget flag (without
# `--autonomous-`, else without `--`) answers `Unknown autonomous budget
# flag: <flag>. <usage>`, whatever follows
# EXCLUDES: an unknown flag accepted or skipped, the `--autonomous-` prefix
#   refused, the value named in the error, a later error reported first
law slash_args_auto_unknown:
  for +s: String
  for +w: String
  for +x: String
  for +t: List<&2, String>
  for ws: {Sa.words(s) == w <> x <> t : List<&2, String>}
  for k: {sa_on(String.to_lower(w)) == True{} : Bool}
  for d: {String.starts_with(x, "--") == True{} : Bool}
  for u: {sa_known(sa_name(sa_raw(x))) == False{} : Bool}
  {Sa.auto(s) == Sa.AErr{sa_err("Unknown autonomous budget flag: ", sa_raw(x))} : Sa.Auto}

# LAW slash_args_auto_missing (R7): after `on`, `enable` or `enabled`
# (lowercased), a first option word x that starts with `--` and names a
# budget flag, with no value given (none: no `=` in x and no next word, or
# one that starts with `--`; or an empty one) answers `Missing value for
# <flag>. <usage>`, whatever follows
# EXCLUDES: a flag word read as the value, a missing value defaulted, an
#   empty value accepted
law slash_args_auto_missing:
  for +s: String
  for +w: String
  for +x: String
  for +t: List<&2, String>
  for ws: {Sa.words(s) == w <> x <> t : List<&2, String>}
  for k: {sa_on(String.to_lower(w)) == True{} : Bool}
  for d: {String.starts_with(x, "--") == True{} : Bool}
  for u: {sa_known(sa_name(sa_raw(x))) == True{} : Bool}
  for g: {sa_given(sa_value(x, t)) == False{} : Bool}
  {Sa.auto(s) == Sa.AErr{sa_err("Missing value for ", sa_raw(x))} : Sa.Auto}

# LAW slash_args_auto_option (R7-R9): after `on`, `enable` or `enabled`
# (lowercased), one option word `--<name>=v` or
# `--autonomous-<name>=v`, for each of the eight flags (k past 7: the
# keep-alive) and every value v,
# answers R8's reading of v for that flag (sa_option; with a limit named,
# the other limits are unlimited), or the missing-value error for an empty v
# EXCLUDES: a flag read as another, the `--autonomous-` prefix refused, a
#   value's `,`/`_` kept, `unlimited` refused for a limit or accepted for a
#   gate number, unnamed limits left unset, a wrong error text
law slash_args_auto_option:
  for +s: String
  for +w: String
  for +p: Bool
  for +k: Nat
  for +v: String
  for ws: {Sa.words(s) == [w, String.append(sa_prefix(p), String.append(sa_flag_name(k), SCon{'=', v}))] : List<&2, String>}
  for on: {sa_on(String.to_lower(w)) == True{} : Bool}
  {Sa.auto(s) == sa_option_or_missing(k, String.append(sa_prefix(p), sa_flag_name(k)), v) : Sa.Auto}

# Anchors
# -------

# LAW slash_args_goal_example (R3-R5): anchor: Rust's vectors, short; the
# value ended by U+3000 (the header's change from the Rust)
# EXCLUDES: a spec that drifts from the Rust it replaced
law slash_args_goal_example:
  {[Sa.goal(""), Sa.goal("Stop"), Sa.goal("PAUSE"), Sa.goal("resume"), Sa.goal("a b"), Sa.goal("--budget 50 go"), Sa.goal("--token-budget=3 x"), Sa.goal("--budget"), Sa.goal("--budget 0x x"), Sa.goal("--budget=5")] == [Sa.GStatus{}, Sa.GClear{}, Sa.GPause{}, Sa.GResume{}, Sa.GStart{"a b", None{}}, Sa.GStart{"go", Some{"50"}}, Sa.GStart{"x", Some{"3"}}, Sa.GErr{"Usage: /goal [--budget <tokens>] <objective>"}, Sa.GErr{"Goal token budget must be a positive integer."}, Sa.GErr{"Goal objective must not be empty."}] : List<&2, Sa.Goal>} &
  {Sa.goal("--budget 5\u{3000}fix it") == Sa.GStart{"fix it", Some{"5"}} : Sa.Goal}

# LAW slash_args_auto_example (R6-R9): anchor: Rust's vectors, short; a
# limit named again (the later value kept), gate commands in order, a gate
# number's `_` dropped (R9); the first bad word's error before a later one
# EXCLUDES: a spec that drifts from the Rust it replaced
law slash_args_auto_example:
  {[Sa.auto(""), Sa.auto("STATUS"), Sa.auto("off"), Sa.auto("on"), Sa.auto("on --max-turns 5 --gate=ls"), Sa.auto("on --subagent-keep-alive-ms 0")] == [Sa.AStatus{}, Sa.AStatus{}, Sa.AOff{}, Sa.AOn{Sa.Conf{None{}, None{}, None{}, None{}, None{}, None{}}}, Sa.AOn{Sa.Conf{Some{Sa.LUnl{}}, Some{Sa.LNum{"5"}}, Some{Sa.LUnl{}}, Some{Sa.LUnl{}}, Some{Sa.Gates{Some{["ls"]}, None{}, None{}}}, None{}}}, Sa.AOn{Sa.Conf{None{}, None{}, None{}, None{}, None{}, Some{"0"}}}] : List<&2, Sa.Auto>} &
  {[Sa.auto("on --max-turns=1 --max-turns 2 --gate a --gate=b --gate-retries 3_0"), Sa.auto("on --gate=x --max-turns=0 --nope 1")] == [Sa.AOn{Sa.Conf{Some{Sa.LUnl{}}, Some{Sa.LNum{"2"}}, Some{Sa.LUnl{}}, Some{Sa.LUnl{}}, Some{Sa.Gates{Some{["a", "b"]}, Some{"30"}, None{}}}, None{}}}, Sa.AErr{String.append("--max-turns must be a positive integer or \"unlimited\". ", sa_usage())}] : List<&2, Sa.Auto>}

# LAW slash_args_auto_errors_example (R6-R8): anchor: the error texts, with
# the usage text sa_usage() spelled out
# EXCLUDES: a spec that drifts from the Rust it replaced
law slash_args_auto_errors_example:
  {[Sa.auto("x"), Sa.auto("status x"), Sa.auto("on x"), Sa.auto("on --no 1"), Sa.auto("on --gate"), Sa.auto("on --max-turns=0"), Sa.auto("on --gate-retries=unlimited")] == [Sa.AErr{sa_usage()}, Sa.AErr{String.append("Unexpected autonomous argument: x. ", sa_usage())}, Sa.AErr{String.append("Unexpected autonomous argument: x. ", sa_usage())}, Sa.AErr{String.append("Unknown autonomous budget flag: --no. ", sa_usage())}, Sa.AErr{String.append("Missing value for --gate. ", sa_usage())}, Sa.AErr{String.append("--max-turns must be a positive integer or \"unlimited\". ", sa_usage())}, Sa.AErr{String.append("--gate-retries must be a positive integer. ", sa_usage())}] : List<&2, Sa.Auto>}

# LAW slash_args_u64_example (R4, R8): anchor: R4's u64 digits at their
# boundaries: 1, 0, a leading 0, 2^64-1, 2^64, a 20-digit value past it,
# 21 digits, empty, a letter; R8's keep-alive digits: 0, 2^31-1, 2^31, a
# leading 0, empty
# EXCLUDES: a u64 test off by one at 2^64, a leading 0 or 0 accepted
law slash_args_u64_example:
  {[Sa.u64("1"), Sa.u64("0"), Sa.u64("01"), Sa.u64("18446744073709551615"), Sa.u64("18446744073709551616"), Sa.u64("99999999999999999999"), Sa.u64("100000000000000000000"), Sa.u64(""), Sa.u64("1a")] == [True{}, False{}, False{}, True{}, False{}, False{}, False{}, False{}, False{}] : List<&2, Bool>} &
  {[Sa.keep_ok("0"), Sa.keep_ok("2147483647"), Sa.keep_ok("2147483648"), Sa.keep_ok("01"), Sa.keep_ok("")] == [True{}, True{}, False{}, False{}, False{}] : List<&2, Bool>}

# LAW slash_args_words_example (R2): anchor: Rust's vectors
# EXCLUDES: a spec that drifts from the Rust it replaced
law slash_args_words_example:
  {[Sa.words("a \"b c\" 'd e' \"\""), Sa.words("  "), Sa.words("a'b'c d")] == [["a", "b c", "d e", ""], [], ["abc", "d"]] : List<&2, List<&2, String>>}
