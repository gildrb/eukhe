# eukhe: the laws of area slash_args: the model (bend/slash_args.bend)

import Base
import ../../bend/slash_args.bend as Sa
import ../gateway_answer.bend as GatewayAnswer

# (D1) The arguments of `/goal` and `/autonomous`, the words of a command
# ------------------------------------------------------------------------
# bend/slash_args.bend, run as the compiled core by bend/ffi_slash_args.bend
# (eukhe-bend rules/slash_args.rs; asked by eukhe-core slash_command_args.rs
# for `/goal` and `/autonomous`, goals.rs for a goal objective, and the
# prompt templates for a command's words). Every input is free: any text.
#
# R1: whitespace is Unicode White_Space (Rust `char::is_whitespace`:
#     GatewayAnswer.ga_white); trimming drops it at both ends. A keyword
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
# <usage> is Sa.auto_usage()'s text, the Rust AUTONOMOUS_BUDGET_USAGE.
# Changed from the Rust it replaced: after `--budget N`, a value ended by a
# multi-byte whitespace char (U+3000, U+00A0, ...) made the Rust slice
# inside that char and panic; the objective is now the text after it.

# Spec helpers: text
# -------------------

def sa_trim_start.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading whitespace
def sa_trim_start(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      sa_trim_start.at(GatewayAnswer.ga_white(c), c, t, sa_trim_start(t))

def sa_trim_end.at(b: Bool, c: Char, r: String) -> String:
  match b:
    case True{}:
      match r:
        case SNil{}:
          SNil{}
        case SCon{x, u}:
          SCon{c, SCon{x, u}}
    case False{}:
      SCon{c, r}

# s without its trailing whitespace
def sa_trim_end(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      sa_trim_end.at(GatewayAnswer.ga_white(c), c, sa_trim_end(t))

def sa_trim(s: String) -> String:
  sa_trim_end(sa_trim_start(s))

# Text before the first whitespace char, and the rest from that char
def sa_cut.at(b: Bool, c: Char, t: String, r: Sa.Cut) -> Sa.Cut:
  match b:
    case True{}:
      Sa.Cut{SNil{}, SCon{c, t}}
    case False{}:
      match r:
        case Sa.Cut{h, u}:
          Sa.Cut{SCon{c, h}, u}

def sa_cut(s: String) -> Sa.Cut:
  match s:
    case SNil{}:
      Sa.Cut{SNil{}, SNil{}}
    case SCon{+c, +t}:
      sa_cut.at(GatewayAnswer.ga_white(c), c, t, sa_cut(t))

# s from just after its first `=` (empty without one)
def sa_after_eq.at(b: Bool, t: String, r: String) -> String:
  match b:
    case True{}:
      t
    case False{}:
      r

def sa_after_eq(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      sa_after_eq.at(Char.is_eq(c, '='), t, sa_after_eq(t))

def sa_all_digits(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Char.is_digit(c), sa_all_digits(t))

# s is digits without a leading 0, one or more (a positive number)
def sa_positive(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +t}:
      Bool.and(Bool.not(Char.is_eq(c, '0')), Bool.and(Char.is_digit(c), sa_all_digits(t)))

# positive digits that a Rust u64 holds
def sa_u64(+s: String) -> Bool:
  +n = String.length(s)
  Bool.and(sa_positive(s), Bool.or(Nat.is_lt(n, 20n), Bool.and(Nat.is_eq(n, 20n), String.is_le(s, "18446744073709551615"))))

# s without its `,` and `_` chars
def sa_ungroup.at(b: Bool, c: Char, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, r}

def sa_ungroup(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      sa_ungroup.at(Bool.or(Char.is_eq(c, ','), Char.is_eq(c, '_')), c, sa_ungroup(t))

# Words
# -----

# The tokenizer's state: the quote open, the word so far (reversed), a
# quote seen in it, the words so far (reversed)
def sa_tok.push(cur: String, quoted: Bool, done: List<&2, String>) -> List<&2, String>:
  match cur:
    case SNil{}:
      match quoted:
        case True{}:
          SNil{} <> done
        case False{}:
          done
    case SCon{c, t}:
      String.reverse(SCon{c, t}) <> done

def sa_tok.in_quote(same: Bool, q: Char, c: Char, cur: String, quoted: Bool, done: List<&2, String>) -> Sa.Tok:
  match same:
    case True{}:
      Sa.Tok{None{}, cur, quoted, done}
    case False{}:
      Sa.Tok{Some{q}, SCon{c, cur}, quoted, done}

def sa_tok.out(opens: Bool, white: Bool, c: Char, cur: String, quoted: Bool, done: List<&2, String>) -> Sa.Tok:
  match opens:
    case True{}:
      Sa.Tok{Some{c}, cur, True{}, done}
    case False{}:
      match white:
        case True{}:
          Sa.Tok{None{}, SNil{}, False{}, sa_tok.push(cur, quoted, done)}
        case False{}:
          Sa.Tok{None{}, SCon{c, cur}, quoted, done}

# one char of the argument text
def sa_tok.step(+c: Char, st: Sa.Tok) -> Sa.Tok:
  match st:
    case Sa.Tok{q, cur, quoted, done}:
      match q:
        case Some{+x}:
          sa_tok.in_quote(Char.is_eq(c, x), x, c, cur, quoted, done)
        case None{}:
          sa_tok.out(Bool.or(Char.is_eq(c, '"'), Char.is_eq(c, '\'')), GatewayAnswer.ga_white(c), c, cur, quoted, done)

def sa_tok.fin(st: Sa.Tok) -> List<&2, String>:
  match st:
    case Sa.Tok{q, cur, quoted, done}:
      List.reverse(&2, String, sa_tok.push(cur, quoted, done))

def sa_tok.go(s: String, st: Sa.Tok) -> List<&2, String>:
  match s:
    case SNil{}:
      sa_tok.fin(st)
    case SCon{+c, t}:
      sa_tok.go(t, sa_tok.step(c, st))

# the words of an argument text
def sa_words(s: String) -> List<&2, String>:
  sa_tok.go(s, Sa.Tok{None{}, SNil{}, False{}, Nil{}})

# /goal
# -----

# What `/goal` asks
def sa_goal_usage() -> String:
  "Usage: /goal [--budget <tokens>] <objective>"

def sa_goal_bad_budget() -> String:
  "Goal token budget must be a positive integer."

def sa_goal.objective.at(empty: Bool, long: Bool, o: String, b: Maybe<&2, String>) -> Sa.Goal:
  match empty:
    case True{}:
      Sa.GErr{"Goal objective must not be empty."}
    case False{}:
      match long:
        case True{}:
          Sa.GErr{"Goal objective must be at most 4000 characters."}
        case False{}:
          Sa.GStart{o, b}

# the objective o (trimmed) with the budget b
def sa_goal.objective(o: String, b: Maybe<&2, String>) -> Sa.Goal:
  +t = sa_trim(o)
  sa_goal.objective.at(String.is_empty(t), Bool.not(Nat.is_le(String.length(t), 4000n)), t, b)

def sa_goal.budget(ok: Bool, v: String, o: String) -> Sa.Goal:
  match ok:
    case True{}:
      sa_goal.objective(o, Some{v})
    case False{}:
      Sa.GErr{sa_goal_bad_budget()}

# `--budget N objective`: the value and the objective after the flag
def sa_goal.spaced(c: Sa.Cut) -> Sa.Goal:
  match c:
    case Sa.Cut{+v, u}:
      match u:
        case SNil{}:
          Sa.GErr{sa_goal_usage()}
        case SCon{w, o}:
          sa_goal.budget(sa_u64(v), v, o)

def sa_goal.flag(bare: Bool, eq: Bool, +first: String, tail: String, rest: String) -> Sa.Goal:
  match bare:
    case True{}:
      sa_goal.spaced(sa_cut(sa_trim_start(tail)))
    case False{}:
      match eq:
        case True{}:
          +v = sa_after_eq(first)
          sa_goal.budget(sa_u64(v), v, tail)
        case False{}:
          sa_goal.objective(rest, None{})

def sa_goal.start(c: Sa.Cut, rest: String) -> Sa.Goal:
  match c:
    case Sa.Cut{+first, tail}:
      sa_goal.flag(Bool.or(String.eq(first, "--budget"), String.eq(first, "--token-budget")), Bool.or(String.starts_with(first, "--budget="), String.starts_with(first, "--token-budget=")), first, tail, rest)

def sa_goal.kw(status: Bool, clear: Bool, pause: Bool, resume: Bool, +rest: String) -> Sa.Goal:
  match status:
    case True{}:
      Sa.GStatus{}
    case False{}:
      match clear:
        case True{}:
          Sa.GClear{}
        case False{}:
          match pause:
            case True{}:
              Sa.GPause{}
            case False{}:
              match resume:
                case True{}:
                  Sa.GResume{}
                case False{}:
                  sa_goal.start(sa_cut(rest), rest)

def sa_goal.of(+rest: String, +l: String) -> Sa.Goal:
  sa_goal.kw(Bool.or(String.is_empty(l), String.eq(l, "status")), Bool.or(String.eq(l, "clear"), String.eq(l, "stop")), String.eq(l, "pause"), String.eq(l, "resume"), rest)

# what `/goal <args>` asks
def sa_goal(args: String) -> Sa.Goal:
  +rest = sa_trim(args)
  sa_goal.of(rest, String.to_lower(rest))

# /autonomous
# -----------

# A limit: unlimited, or its digits
# The gate options named: the commands, retries and timeout digits
# The options of `/autonomous on`
# What `/autonomous` asks
def sa_auto_usage() -> String:
  "Usage: /autonomous [status|off] or /autonomous on [--max-continuations <n|unlimited>] [--max-turns <n|unlimited>] [--max-tokens <n|unlimited>] [--timeout-ms <n|unlimited>] [--gate <command>] [--gate-retries <n>] [--gate-timeout-ms <n>] [--subagent-keep-alive-ms <n>]"

# `<head>: <word>. <usage>`
def sa_auto_err(+head: String, w: String) -> String:
  String.append(head, String.append(w, String.append(". ", sa_auto_usage())))

# The options read so far: each value named, the gate commands in order,
# whether a gate retry or timeout was named
# Options read, or the first bad word's error
def sa_opts.none() -> Sa.Opts:
  Sa.Opts{None{}, None{}, None{}, None{}, Nil{}, False{}, None{}, None{}, None{}}

# the later of two values: b when named
def sa_later(-A: Data, a: Maybe<&2, A>, b: Maybe<&2, A>) -> Maybe<&2, A>:
  match b:
    case None{}:
      a
    case Some{x}:
      Some{x}

# the options a, then the options b read after them
def sa_opts.then(a: Sa.Opts, b: Sa.Opts) -> Sa.Opts:
  match a:
    case Sa.Opts{c1, t1, k1, m1, g1, d1, r1, s1, p1}:
      match b:
        case Sa.Opts{c2, t2, k2, m2, g2, d2, r2, s2, p2}:
          Sa.Opts{sa_later(Sa.Lim, c1, c2), sa_later(Sa.Lim, t1, t2), sa_later(Sa.Lim, k1, k2), sa_later(Sa.Lim, m1, m2), List.append(&2, String, g1, g2), Bool.or(d1, d2), sa_later(String, r1, r2), sa_later(String, s1, s2), sa_later(String, p1, p2)}

def sa_read.then(a: Sa.Read, b: Sa.Read) -> Sa.Read:
  match a:
    case Sa.ROk{x}:
      match b:
        case Sa.ROk{y}:
          Sa.ROk{sa_opts.then(x, y)}
        case Sa.RErr{e}:
          Sa.RErr{e}
    case Sa.RErr{e}:
      Sa.RErr{e}

def sa_int_err(+name: String, unl: Bool) -> String:
  match unl:
    case True{}:
      String.append("--", String.append(name, String.append(" must be a positive integer or \"unlimited\". ", sa_auto_usage())))
    case False{}:
      String.append("--", String.append(name, String.append(" must be a positive integer. ", sa_auto_usage())))

def sa_lim.num(ok: Bool, d: String) -> Maybe<&2, Sa.Lim>:
  match ok:
    case True{}:
      Some{Sa.LNum{d}}
    case False{}:
      None{}

# a limit's value: `unlimited`, or digits
def sa_lim.of(unl: Bool, +v: String) -> Maybe<&2, Sa.Lim>:
  match unl:
    case True{}:
      Some{Sa.LUnl{}}
    case False{}:
      +d = sa_ungroup(v)
      sa_lim.num(sa_u64(d), d)

def sa_opt.lim(+name: String, m: Maybe<&2, Sa.Lim>, k: Nat) -> Sa.Read:
  match m:
    case None{}:
      Sa.RErr{sa_int_err(name, True{})}
    case Some{l}:
      match k:
        case 0n:
          Sa.ROk{Sa.Opts{Some{l}, None{}, None{}, None{}, Nil{}, False{}, None{}, None{}, None{}}}
        case 1n:
          Sa.ROk{Sa.Opts{None{}, Some{l}, None{}, None{}, Nil{}, False{}, None{}, None{}, None{}}}
        case 2n:
          Sa.ROk{Sa.Opts{None{}, None{}, Some{l}, None{}, Nil{}, False{}, None{}, None{}, None{}}}
        case 3n+u:
          Sa.ROk{Sa.Opts{None{}, None{}, None{}, Some{l}, Nil{}, False{}, None{}, None{}, None{}}}

# a gate number: digits only
def sa_opt.gate(+name: String, ok: Bool, d: String, retries: Bool) -> Sa.Read:
  match ok:
    case True{}:
      match retries:
        case True{}:
          Sa.ROk{Sa.Opts{None{}, None{}, None{}, None{}, Nil{}, True{}, Some{d}, None{}, None{}}}
        case False{}:
          Sa.ROk{Sa.Opts{None{}, None{}, None{}, None{}, Nil{}, True{}, None{}, Some{d}, None{}}}
    case False{}:
      Sa.RErr{sa_int_err(name, False{})}

def sa_keep_err() -> String:
  String.append("--subagent-keep-alive-ms must be 0 or a positive integer up to 2147483647. ", sa_auto_usage())

def sa_opt.keep(ok: Bool, d: String) -> Sa.Read:
  match ok:
    case True{}:
      Sa.ROk{Sa.Opts{None{}, None{}, None{}, None{}, Nil{}, False{}, None{}, None{}, Some{d}}}
    case False{}:
      Sa.RErr{sa_keep_err()}

# keep-alive digits: 0, or positive up to 2147483647
def sa_keep_ok(+d: String) -> Bool:
  +n = String.length(d)
  Bool.or(String.eq(d, "0"), Bool.and(sa_positive(d), Bool.or(Nat.is_lt(n, 10n), Bool.and(Nat.is_eq(n, 10n), String.is_le(d, "2147483647")))))

# The flags, in order
def sa_flags() -> List<&2, String>:
  ["max-continuations", "max-turns", "max-tokens", "timeout-ms", "gate", "gate-retries", "gate-timeout-ms", "subagent-keep-alive-ms"]

def sa_index.at(b: Bool, i: Nat, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{i}
    case False{}:
      r

# the index of n in xs, counted from i
def sa_index(+n: String, xs: List<&2, String>, +i: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case x <> t:
      sa_index.at(String.eq(n, x), i, sa_index(n, t, 1n+i))

# the option of flag index k with the value v
def sa_opt.value(k: Nat, +name: String, +v: String) -> Sa.Read:
  match k:
    case 0n:
      sa_opt.lim(name, sa_lim.of(String.eq(String.to_lower(v), "unlimited"), v), 0n)
    case 1n:
      sa_opt.lim(name, sa_lim.of(String.eq(String.to_lower(v), "unlimited"), v), 1n)
    case 2n:
      sa_opt.lim(name, sa_lim.of(String.eq(String.to_lower(v), "unlimited"), v), 2n)
    case 3n:
      sa_opt.lim(name, sa_lim.of(String.eq(String.to_lower(v), "unlimited"), v), 3n)
    case 4n:
      Sa.ROk{Sa.Opts{None{}, None{}, None{}, None{}, [v], False{}, None{}, None{}, None{}}}
    case 5n:
      +d = sa_ungroup(v)
      sa_opt.gate(name, sa_u64(d), d, True{})
    case 6n:
      +d = sa_ungroup(v)
      sa_opt.gate(name, sa_u64(d), d, False{})
    case 7n+u:
      +d = sa_ungroup(v)
      sa_opt.keep(sa_keep_ok(d), d)

# The value of an option: given with `=`, or the next word
def sa_val.next.at(flag: Bool, w: String) -> Sa.Val:
  match flag:
    case True{}:
      Sa.VNone{}
    case False{}:
      Sa.VAt{w, True{}}

def sa_val.next(ws: List<&2, String>) -> Sa.Val:
  match ws:
    case Nil{}:
      Sa.VNone{}
    case +w <> t:
      sa_val.next.at(String.starts_with(w, "--"), w)

def sa_val.of(eq: Bool, +tok: String, ws: List<&2, String>) -> Sa.Val:
  match eq:
    case True{}:
      Sa.VAt{sa_after_eq(tok), False{}}
    case False{}:
      sa_val.next(ws)

# the flag of a word: before its first `=`
def sa_before_eq.at(b: Bool, c: Char, r: String) -> String:
  match b:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, r}

def sa_before_eq(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      sa_before_eq.at(Char.is_eq(c, '='), c, sa_before_eq(t))

# the flag's name: without `--autonomous-`, else without `--`
def sa_name.dashes(b: Bool, raw: String) -> String:
  match b:
    case True{}:
      String.drop(raw, 2n)
    case False{}:
      raw

def sa_name.of(b: Bool, +raw: String) -> String:
  match b:
    case True{}:
      String.drop(raw, 13n)
    case False{}:
      sa_name.dashes(String.starts_with(raw, "--"), raw)

# One step of the options: the option of the word w (with the next word
# when it takes it), the reads of the words after w (r1) and after the
# next word (r2)
def sa_step.took(empty: Bool, took: Bool, +raw: String, k: Nat, +name: String, x: String, r1: Sa.Read, r2: Sa.Read) -> Sa.Read:
  match empty:
    case True{}:
      Sa.RErr{sa_auto_err("Missing value for ", raw)}
    case False{}:
      match took:
        case True{}:
          sa_read.then(sa_opt.value(k, name, x), r2)
        case False{}:
          sa_read.then(sa_opt.value(k, name, x), r1)

def sa_step.val(v: Sa.Val, +raw: String, k: Nat, +name: String, r1: Sa.Read, r2: Sa.Read) -> Sa.Read:
  match v:
    case Sa.VNone{}:
      Sa.RErr{sa_auto_err("Missing value for ", raw)}
    case Sa.VAt{+x, took}:
      sa_step.took(String.is_empty(x), took, raw, k, name, x, r1, r2)

def sa_step.known(m: Maybe<&2, Nat>, +w: String, +raw: String, +name: String, ws: List<&2, String>, r1: Sa.Read, r2: Sa.Read) -> Sa.Read:
  match m:
    case None{}:
      Sa.RErr{sa_auto_err("Unknown autonomous budget flag: ", raw)}
    case Some{k}:
      sa_step.val(sa_val.of(String.contains(w, "="), w, ws), raw, k, name, r1, r2)

def sa_step.flag(+w: String, ws: List<&2, String>, r1: Sa.Read, r2: Sa.Read) -> Sa.Read:
  +raw = sa_before_eq(w)
  +name = sa_name.of(String.starts_with(raw, "--autonomous-"), raw)
  sa_step.known(sa_index(name, sa_flags(), 0n), w, raw, name, ws, r1, r2)

def sa_step(dash: Bool, +w: String, ws: List<&2, String>, r1: Sa.Read, r2: Sa.Read) -> Sa.Read:
  match dash:
    case True{}:
      sa_step.flag(w, ws, r1, r2)
    case False{}:
      Sa.RErr{sa_auto_err("Unexpected autonomous argument: ", w)}

def sa_reads.of(+w: String, +t: List<&2, String>, rr: Sa.Read & Sa.Read) -> Sa.Read & Sa.Read:
  (r1, r2) = rr
  +x = r1
  (sa_step(String.starts_with(w, "--"), w, t, x, r2), x)

# the reads of ws and of ws without its first word
def sa_reads(ws: List<&2, String>) -> Sa.Read & Sa.Read:
  match ws:
    case Nil{}:
      (Sa.ROk{sa_opts.none()}, Sa.ROk{sa_opts.none()})
    case +w <> +t:
      sa_reads.of(w, t, sa_reads(t))

# the options of the words ws
def sa_options.fst(rr: Sa.Read & Sa.Read) -> Sa.Read:
  (r, s) = rr
  r

def sa_options(ws: List<&2, String>) -> Sa.Read:
  sa_options.fst(sa_reads(ws))

def sa_unl(m: Maybe<&2, Sa.Lim>) -> Maybe<&2, Sa.Lim>:
  match m:
    case None{}:
      Some{Sa.LUnl{}}
    case Some{l}:
      Some{l}

def sa_conf.gates(cmds: List<&2, String>, gated: Bool, r: Maybe<&2, String>, s: Maybe<&2, String>) -> Maybe<&2, Sa.Gates>:
  match cmds:
    case Nil{}:
      match gated:
        case True{}:
          Some{Sa.Gates{None{}, r, s}}
        case False{}:
          None{}
    case c <> t:
      Some{Sa.Gates{Some{c <> t}, r, s}}

def sa_conf.limits(named: Bool, c: Maybe<&2, Sa.Lim>, t: Maybe<&2, Sa.Lim>, k: Maybe<&2, Sa.Lim>, m: Maybe<&2, Sa.Lim>, g: Maybe<&2, Sa.Gates>, p: Maybe<&2, String>) -> Sa.Conf:
  match named:
    case True{}:
      Sa.Conf{sa_unl(c), sa_unl(t), sa_unl(k), sa_unl(m), g, p}
    case False{}:
      Sa.Conf{c, t, k, m, g, p}

def sa_some(-A: Data, m: Maybe<&2, A>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

# the options read, as `/autonomous on` takes them
def sa_conf(o: Sa.Opts) -> Sa.Conf:
  match o:
    case Sa.Opts{+c, +t, +k, +m, g, d, r, s, p}:
      sa_conf.limits(Bool.or(Bool.or(sa_some(Sa.Lim, c), sa_some(Sa.Lim, t)), Bool.or(sa_some(Sa.Lim, k), sa_some(Sa.Lim, m))), c, t, k, m, sa_conf.gates(g, d, r, s), p)

def sa_auto.on(r: Sa.Read) -> Sa.Auto:
  match r:
    case Sa.ROk{o}:
      Sa.AOn{sa_conf(o)}
    case Sa.RErr{e}:
      Sa.AErr{e}

def sa_auto.alone(ws: List<&2, String>, a: Sa.Auto) -> Sa.Auto:
  match ws:
    case Nil{}:
      a
    case w <> t:
      Sa.AErr{sa_auto_err("Unexpected autonomous argument: ", w)}

def sa_auto.kw(status: Bool, on: Bool, off: Bool, ws: List<&2, String>) -> Sa.Auto:
  match status:
    case True{}:
      sa_auto.alone(ws, Sa.AStatus{})
    case False{}:
      match on:
        case True{}:
          sa_auto.on(sa_options(ws))
        case False{}:
          match off:
            case True{}:
              sa_auto.alone(ws, Sa.AOff{})
            case False{}:
              Sa.AErr{sa_auto_usage()}

def sa_auto.first(+l: String, ws: List<&2, String>) -> Sa.Auto:
  sa_auto.kw(String.eq(l, "status"), Bool.or(String.eq(l, "on"), Bool.or(String.eq(l, "enable"), String.eq(l, "enabled"))), Bool.or(String.eq(l, "off"), Bool.or(String.eq(l, "disable"), String.eq(l, "disabled"))), ws)

def sa_auto.words(ws: List<&2, String>) -> Sa.Auto:
  match ws:
    case Nil{}:
      Sa.AStatus{}
    case w <> t:
      sa_auto.first(String.to_lower(w), t)

# what `/autonomous <args>` asks
def sa_auto(args: String) -> Sa.Auto:
  sa_auto.words(sa_words(args))

# Laws: the model
# ---------------

# LAW slash_args_words_spec (R1, R2): the words of every text are the
# spec's
# EXCLUDES: ASCII-only whitespace, a quote closed by the other quote char,
#   an empty quoted word dropped, an unquoted empty word kept, the last
#   word lost, quote chars kept
law slash_args_words_spec:
  for +s: String
  {Sa.words(s) == sa_words(s) : List<&2, String>}

# LAW slash_args_goal_spec (R1, R3-R5): what every `/goal` text asks is the
# spec's
# EXCLUDES: a case-sensitive keyword, `stop` not clearing, a budget flag
#   read anywhere but first, a value with a leading 0 or past u64 taken, the
#   usage error lost, an untrimmed or overlong objective, an empty
#   objective started
law slash_args_goal_spec:
  for +s: String
  {Sa.goal(s) == sa_goal(s) : Sa.Goal}

# LAW slash_args_objective_spec (R5): every objective alone is judged as
# the spec judges it
# EXCLUDES: a limit off by one, an objective kept untrimmed
law slash_args_objective_spec:
  for +s: String
  for +b: Maybe<&2, String>
  {Sa.goal.objective(s, b) == sa_goal.objective(s, b) : Sa.Goal}

# LAW slash_args_auto_spec (R1, R2, R6-R9): what every `/autonomous` text
# asks is the spec's
# EXCLUDES: a word after `status`/`off` ignored, an unknown flag accepted,
#   the `--autonomous-` prefix refused, a value taken from a flag word, an
#   empty value accepted, `unlimited` for a gate number, a keep-alive past
#   2147483647, the first value of a repeated flag kept, gate commands out
#   of order, unnamed limits left unset after a named one, a later error
#   reported before an earlier one
law slash_args_auto_spec:
  for +s: String
  {Sa.auto(s) == sa_auto(s) : Sa.Auto}

# LAW slash_args_goal_example (R3-R5): anchor: Rust's vectors, short
# EXCLUDES: a spec that drifts from the Rust it replaced
law slash_args_goal_example:
  {[Sa.goal(""), Sa.goal("Stop"), Sa.goal("PAUSE"), Sa.goal("resume"), Sa.goal("a b"), Sa.goal("--budget 50 go"), Sa.goal("--token-budget=3 x"), Sa.goal("--budget"), Sa.goal("--budget 0x x"), Sa.goal("--budget=5")] == [Sa.GStatus{}, Sa.GClear{}, Sa.GPause{}, Sa.GResume{}, Sa.GStart{"a b", None{}}, Sa.GStart{"go", Some{"50"}}, Sa.GStart{"x", Some{"3"}}, Sa.GErr{"Usage: /goal [--budget <tokens>] <objective>"}, Sa.GErr{"Goal token budget must be a positive integer."}, Sa.GErr{"Goal objective must not be empty."}] : List<&2, Sa.Goal>}

# LAW slash_args_auto_example (R6-R9): anchor: Rust's vectors, short
# EXCLUDES: a spec that drifts from the Rust it replaced
law slash_args_auto_example:
  {[Sa.auto(""), Sa.auto("STATUS"), Sa.auto("off"), Sa.auto("on"), Sa.auto("on --max-turns 5 --gate=ls"), Sa.auto("on --subagent-keep-alive-ms 0")] == [Sa.AStatus{}, Sa.AStatus{}, Sa.AOff{}, Sa.AOn{Sa.Conf{None{}, None{}, None{}, None{}, None{}, None{}}}, Sa.AOn{Sa.Conf{Some{Sa.LUnl{}}, Some{Sa.LNum{"5"}}, Some{Sa.LUnl{}}, Some{Sa.LUnl{}}, Some{Sa.Gates{Some{["ls"]}, None{}, None{}}}, None{}}}, Sa.AOn{Sa.Conf{None{}, None{}, None{}, None{}, None{}, Some{"0"}}}] : List<&2, Sa.Auto>}

# LAW slash_args_auto_errors_example (R6-R8): anchor: the error texts
# EXCLUDES: a spec that drifts from the Rust it replaced
law slash_args_auto_errors_example:
  {[Sa.auto("x"), Sa.auto("status x"), Sa.auto("on x"), Sa.auto("on --no 1"), Sa.auto("on --gate"), Sa.auto("on --max-turns=0"), Sa.auto("on --gate-retries=unlimited")] == [Sa.AErr{Sa.auto_usage()}, Sa.AErr{String.append("Unexpected autonomous argument: x. ", Sa.auto_usage())}, Sa.AErr{String.append("Unexpected autonomous argument: x. ", Sa.auto_usage())}, Sa.AErr{String.append("Unknown autonomous budget flag: --no. ", Sa.auto_usage())}, Sa.AErr{String.append("Missing value for --gate. ", Sa.auto_usage())}, Sa.AErr{String.append("--max-turns must be a positive integer or \"unlimited\". ", Sa.auto_usage())}, Sa.AErr{String.append("--gate-retries must be a positive integer. ", Sa.auto_usage())}] : List<&2, Sa.Auto>}

# LAW slash_args_usage_example (R6): the usage text is Rust's
# AUTONOMOUS_BUDGET_USAGE
# EXCLUDES: a changed usage text
law slash_args_usage_example:
  {Sa.auto_usage() == "Usage: /autonomous [status|off] or /autonomous on [--max-continuations <n|unlimited>] [--max-turns <n|unlimited>] [--max-tokens <n|unlimited>] [--timeout-ms <n|unlimited>] [--gate <command>] [--gate-retries <n>] [--gate-timeout-ms <n>] [--subagent-keep-alive-ms <n>]" : String}

# LAW slash_args_words_example (R2): anchor: Rust's vectors
# EXCLUDES: a spec that drifts from the Rust it replaced
law slash_args_words_example:
  {[Sa.words("a \"b c\" 'd e' \"\""), Sa.words("  "), Sa.words("a'b'c d")] == [["a", "b c", "d e", ""], [], ["abc", "d"]] : List<&2, List<&2, String>>}
