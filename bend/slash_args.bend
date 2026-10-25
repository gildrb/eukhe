# slash_args: the arguments of the session slash commands `/goal` and
# `/autonomous`, and the quote-aware words of a command's argument text
# (Rust: eukhe-bend rules/slash_args.rs; asked by eukhe-core
# slash_command_args.rs for `/goal` and `/autonomous`, and by the prompt
# templates for `$1`, `$@`). Whitespace is Unicode White_Space (Rust
# `char::is_whitespace`, gateway_answer's `space`); a keyword compares
# with the text's ASCII letters lowercased (no other char lowercases to
# an ASCII letter of a keyword).
#
# Words: chars outside quotes split at whitespace; `"` or `'` opens a
# quote that the same char closes, its chars kept (whitespace too); a
# quoted word is a word even when empty.
#
# `/goal`: the trimmed text, lowercased, is empty or `status`, `clear` or
# `stop`, `pause`, `resume`; else its first whitespace-separated piece may
# be `--budget N` / `--token-budget N` (the value up to the next
# whitespace, the objective after it) or `--budget=N` / `--token-budget=N`
# (the objective after the piece); N must be digits without a leading 0,
# at most 18446744073709551615; the objective, trimmed, must not be empty
# and holds at most 4000 chars.
#
# `/autonomous`: no words or `status` alone: the status; `on`, `enable`,
# `enabled` then budget options; `off`, `disable`, `disabled` alone. An
# option is `--<flag>` or `--autonomous-<flag>`, its value after `=` or
# the next word (not one opening `--`), never empty. Limits take digits
# (`,` and `_` dropped) without a leading 0, at most 18446744073709551615,
# or `unlimited`; gate retries and timeouts the same without `unlimited`;
# the keep-alive 0 or such digits up to 2147483647; `--gate` adds a
# command. A later option overrides an earlier one; the first bad word
# answers its error. Once a limit is named, every limit not named is
# unlimited.
# Pure: no IO, no @unsafe.

import Base
import ./gateway_answer.bend as Ga

# Text
# ----

def trim_start.at(b: Bool, c: Char, t: String, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, t}

# s without its leading whitespace
def trim_start(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      trim_start.at(Ga.space(c), c, t, trim_start(t))

def trim_end.at(b: Bool, c: Char, r: String) -> String:
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
def trim_end(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      trim_end.at(Ga.space(c), c, trim_end(t))

def trim(s: String) -> String:
  trim_end(trim_start(s))

# Text before the first whitespace char, and the rest from that char
type Cut is Data:
  Cut{head: String, tail: String}

def cut.at(b: Bool, c: Char, t: String, r: Cut) -> Cut:
  match b:
    case True{}:
      Cut{SNil{}, SCon{c, t}}
    case False{}:
      match r:
        case Cut{h, u}:
          Cut{SCon{c, h}, u}

def cut(s: String) -> Cut:
  match s:
    case SNil{}:
      Cut{SNil{}, SNil{}}
    case SCon{+c, +t}:
      cut.at(Ga.space(c), c, t, cut(t))

# s from just after its first `=` (empty without one)
def after_eq.at(b: Bool, t: String, r: String) -> String:
  match b:
    case True{}:
      t
    case False{}:
      r

def after_eq(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, +t}:
      after_eq.at(Char.is_eq(c, '='), t, after_eq(t))

def all_digits(s: String) -> Bool:
  match s:
    case SNil{}:
      True{}
    case SCon{c, t}:
      Bool.and(Char.is_digit(c), all_digits(t))

# s is digits without a leading 0, one or more (a positive number)
def positive(s: String) -> Bool:
  match s:
    case SNil{}:
      False{}
    case SCon{+c, +t}:
      Bool.and(Bool.not(Char.is_eq(c, '0')), Bool.and(Char.is_digit(c), all_digits(t)))

# positive digits that a Rust u64 holds
def u64(+s: String) -> Bool:
  +n = String.length(s)
  Bool.and(positive(s), Bool.or(Nat.is_lt(n, 20n), Bool.and(Nat.is_eq(n, 20n), String.is_le(s, "18446744073709551615"))))

# s without its `,` and `_` chars
def ungroup.at(b: Bool, c: Char, r: String) -> String:
  match b:
    case True{}:
      r
    case False{}:
      SCon{c, r}

def ungroup(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      ungroup.at(Bool.or(Char.is_eq(c, ','), Char.is_eq(c, '_')), c, ungroup(t))

# Words
# -----

# The tokenizer's state: the quote open, the word so far (reversed), a
# quote seen in it, the words so far (reversed)
type Tok is Data:
  Tok{quote: Maybe<&2, Char>, cur: String, quoted: Bool, done: List<&2, String>}

def tok.push(cur: String, quoted: Bool, done: List<&2, String>) -> List<&2, String>:
  match cur:
    case SNil{}:
      match quoted:
        case True{}:
          SNil{} <> done
        case False{}:
          done
    case SCon{c, t}:
      String.reverse(SCon{c, t}) <> done

def tok.in_quote(same: Bool, q: Char, c: Char, cur: String, quoted: Bool, done: List<&2, String>) -> Tok:
  match same:
    case True{}:
      Tok{None{}, cur, quoted, done}
    case False{}:
      Tok{Some{q}, SCon{c, cur}, quoted, done}

def tok.out(opens: Bool, white: Bool, c: Char, cur: String, quoted: Bool, done: List<&2, String>) -> Tok:
  match opens:
    case True{}:
      Tok{Some{c}, cur, True{}, done}
    case False{}:
      match white:
        case True{}:
          Tok{None{}, SNil{}, False{}, tok.push(cur, quoted, done)}
        case False{}:
          Tok{None{}, SCon{c, cur}, quoted, done}

# one char of the argument text
def tok.step(+c: Char, st: Tok) -> Tok:
  match st:
    case Tok{q, cur, quoted, done}:
      match q:
        case Some{+x}:
          tok.in_quote(Char.is_eq(c, x), x, c, cur, quoted, done)
        case None{}:
          tok.out(Bool.or(Char.is_eq(c, '"'), Char.is_eq(c, '\'')), Ga.space(c), c, cur, quoted, done)

def tok.fin(st: Tok) -> List<&2, String>:
  match st:
    case Tok{q, cur, quoted, done}:
      List.reverse(&2, String, tok.push(cur, quoted, done))

def tok.go(s: String, st: Tok) -> List<&2, String>:
  match s:
    case SNil{}:
      tok.fin(st)
    case SCon{+c, t}:
      tok.go(t, tok.step(c, st))

# the words of an argument text
def words(s: String) -> List<&2, String>:
  tok.go(s, Tok{None{}, SNil{}, False{}, Nil{}})

# /goal
# -----

# What `/goal` asks
type Goal is Data:
  GStatus{}
  GClear{}
  GPause{}
  GResume{}
  # the objective and the token budget's digits
  GStart{objective: String, budget: Maybe<&2, String>}
  GErr{text: String}

def goal_usage() -> String:
  "Usage: /goal [--budget <tokens>] <objective>"

def goal_bad_budget() -> String:
  "Goal token budget must be a positive integer."

def goal.objective.at(empty: Bool, long: Bool, o: String, b: Maybe<&2, String>) -> Goal:
  match empty:
    case True{}:
      GErr{"Goal objective must not be empty."}
    case False{}:
      match long:
        case True{}:
          GErr{"Goal objective must be at most 4000 characters."}
        case False{}:
          GStart{o, b}

# the objective o (trimmed) with the budget b
def goal.objective(o: String, b: Maybe<&2, String>) -> Goal:
  +t = trim(o)
  goal.objective.at(String.is_empty(t), Bool.not(Nat.is_le(String.length(t), 4000n)), t, b)

def goal.budget(ok: Bool, v: String, o: String) -> Goal:
  match ok:
    case True{}:
      goal.objective(o, Some{v})
    case False{}:
      GErr{goal_bad_budget()}

# `--budget N objective`: the value and the objective after the flag
def goal.spaced(c: Cut) -> Goal:
  match c:
    case Cut{+v, u}:
      match u:
        case SNil{}:
          GErr{goal_usage()}
        case SCon{w, o}:
          goal.budget(u64(v), v, o)

def goal.flag(bare: Bool, eq: Bool, +first: String, tail: String, rest: String) -> Goal:
  match bare:
    case True{}:
      goal.spaced(cut(trim_start(tail)))
    case False{}:
      match eq:
        case True{}:
          +v = after_eq(first)
          goal.budget(u64(v), v, tail)
        case False{}:
          goal.objective(rest, None{})

def goal.start(c: Cut, rest: String) -> Goal:
  match c:
    case Cut{+first, tail}:
      goal.flag(Bool.or(String.eq(first, "--budget"), String.eq(first, "--token-budget")), Bool.or(String.starts_with(first, "--budget="), String.starts_with(first, "--token-budget=")), first, tail, rest)

def goal.kw(status: Bool, clear: Bool, pause: Bool, resume: Bool, +rest: String) -> Goal:
  match status:
    case True{}:
      GStatus{}
    case False{}:
      match clear:
        case True{}:
          GClear{}
        case False{}:
          match pause:
            case True{}:
              GPause{}
            case False{}:
              match resume:
                case True{}:
                  GResume{}
                case False{}:
                  goal.start(cut(rest), rest)

def goal.of(+rest: String, +l: String) -> Goal:
  goal.kw(Bool.or(String.is_empty(l), String.eq(l, "status")), Bool.or(String.eq(l, "clear"), String.eq(l, "stop")), String.eq(l, "pause"), String.eq(l, "resume"), rest)

# what `/goal <args>` asks
def goal(args: String) -> Goal:
  +rest = trim(args)
  goal.of(rest, String.to_lower(rest))

# /autonomous
# -----------

# A limit: unlimited, or its digits
type Lim is Data:
  LUnl{}
  LNum{digits: String}

# The gate options named: the commands, retries and timeout digits
type Gates is Data:
  Gates{commands: Maybe<&2, List<&2, String>>, retries: Maybe<&2, String>, timeout: Maybe<&2, String>}

# The options of `/autonomous on`
type Conf is Data:
  Conf{cont: Maybe<&2, Lim>, turns: Maybe<&2, Lim>, tokens: Maybe<&2, Lim>, timeout: Maybe<&2, Lim>, gates: Maybe<&2, Gates>, keep: Maybe<&2, String>}

# What `/autonomous` asks
type Auto is Data:
  AStatus{}
  AOn{conf: Conf}
  AOff{}
  AErr{text: String}

def auto_usage() -> String:
  "Usage: /autonomous [status|off] or /autonomous on [--max-continuations <n|unlimited>] [--max-turns <n|unlimited>] [--max-tokens <n|unlimited>] [--timeout-ms <n|unlimited>] [--gate <command>] [--gate-retries <n>] [--gate-timeout-ms <n>] [--subagent-keep-alive-ms <n>]"

# `<head>: <word>. <usage>`
def auto_err(+head: String, w: String) -> String:
  String.append(head, String.append(w, String.append(". ", auto_usage())))

# The options read so far: each value named, the gate commands in order,
# whether a gate retry or timeout was named
type Opts is Data:
  Opts{cont: Maybe<&2, Lim>, turns: Maybe<&2, Lim>, tokens: Maybe<&2, Lim>, timeout: Maybe<&2, Lim>, cmds: List<&2, String>, gated: Bool, retries: Maybe<&2, String>, gtimeout: Maybe<&2, String>, keep: Maybe<&2, String>}

# Options read, or the first bad word's error
type Read is Data:
  ROk{opts: Opts}
  RErr{text: String}

def opts.none() -> Opts:
  Opts{None{}, None{}, None{}, None{}, Nil{}, False{}, None{}, None{}, None{}}

# the later of two values: b when named
def later(-A: Data, a: Maybe<&2, A>, b: Maybe<&2, A>) -> Maybe<&2, A>:
  match b:
    case None{}:
      a
    case Some{x}:
      Some{x}

# the options a, then the options b read after them
def opts.then(a: Opts, b: Opts) -> Opts:
  match a:
    case Opts{c1, t1, k1, m1, g1, d1, r1, s1, p1}:
      match b:
        case Opts{c2, t2, k2, m2, g2, d2, r2, s2, p2}:
          Opts{later(Lim, c1, c2), later(Lim, t1, t2), later(Lim, k1, k2), later(Lim, m1, m2), List.append(&2, String, g1, g2), Bool.or(d1, d2), later(String, r1, r2), later(String, s1, s2), later(String, p1, p2)}

def read.then(a: Read, b: Read) -> Read:
  match a:
    case ROk{x}:
      match b:
        case ROk{y}:
          ROk{opts.then(x, y)}
        case RErr{e}:
          RErr{e}
    case RErr{e}:
      RErr{e}

def int_err(+name: String, unl: Bool) -> String:
  match unl:
    case True{}:
      String.append("--", String.append(name, String.append(" must be a positive integer or \"unlimited\". ", auto_usage())))
    case False{}:
      String.append("--", String.append(name, String.append(" must be a positive integer. ", auto_usage())))

def lim.num(ok: Bool, d: String) -> Maybe<&2, Lim>:
  match ok:
    case True{}:
      Some{LNum{d}}
    case False{}:
      None{}

# a limit's value: `unlimited`, or digits
def lim.of(unl: Bool, +v: String) -> Maybe<&2, Lim>:
  match unl:
    case True{}:
      Some{LUnl{}}
    case False{}:
      +d = ungroup(v)
      lim.num(u64(d), d)

def opt.lim(+name: String, m: Maybe<&2, Lim>, k: Nat) -> Read:
  match m:
    case None{}:
      RErr{int_err(name, True{})}
    case Some{l}:
      match k:
        case 0n:
          ROk{Opts{Some{l}, None{}, None{}, None{}, Nil{}, False{}, None{}, None{}, None{}}}
        case 1n:
          ROk{Opts{None{}, Some{l}, None{}, None{}, Nil{}, False{}, None{}, None{}, None{}}}
        case 2n:
          ROk{Opts{None{}, None{}, Some{l}, None{}, Nil{}, False{}, None{}, None{}, None{}}}
        case 3n+u:
          ROk{Opts{None{}, None{}, None{}, Some{l}, Nil{}, False{}, None{}, None{}, None{}}}

# a gate number: digits only
def opt.gate(+name: String, ok: Bool, d: String, retries: Bool) -> Read:
  match ok:
    case True{}:
      match retries:
        case True{}:
          ROk{Opts{None{}, None{}, None{}, None{}, Nil{}, True{}, Some{d}, None{}, None{}}}
        case False{}:
          ROk{Opts{None{}, None{}, None{}, None{}, Nil{}, True{}, None{}, Some{d}, None{}}}
    case False{}:
      RErr{int_err(name, False{})}

def keep_err() -> String:
  String.append("--subagent-keep-alive-ms must be 0 or a positive integer up to 2147483647. ", auto_usage())

def opt.keep(ok: Bool, d: String) -> Read:
  match ok:
    case True{}:
      ROk{Opts{None{}, None{}, None{}, None{}, Nil{}, False{}, None{}, None{}, Some{d}}}
    case False{}:
      RErr{keep_err()}

# keep-alive digits: 0, or positive up to 2147483647
def keep_ok(+d: String) -> Bool:
  +n = String.length(d)
  Bool.or(String.eq(d, "0"), Bool.and(positive(d), Bool.or(Nat.is_lt(n, 10n), Bool.and(Nat.is_eq(n, 10n), String.is_le(d, "2147483647")))))

# The flags, in order
def flags() -> List<&2, String>:
  ["max-continuations", "max-turns", "max-tokens", "timeout-ms", "gate", "gate-retries", "gate-timeout-ms", "subagent-keep-alive-ms"]

def index.at(b: Bool, i: Nat, r: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match b:
    case True{}:
      Some{i}
    case False{}:
      r

# the index of n in xs, counted from i
def index(+n: String, xs: List<&2, String>, +i: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case x <> t:
      index.at(String.eq(n, x), i, index(n, t, 1n+i))

# the option of flag index k with the value v
def opt.value(k: Nat, +name: String, +v: String) -> Read:
  match k:
    case 0n:
      opt.lim(name, lim.of(String.eq(String.to_lower(v), "unlimited"), v), 0n)
    case 1n:
      opt.lim(name, lim.of(String.eq(String.to_lower(v), "unlimited"), v), 1n)
    case 2n:
      opt.lim(name, lim.of(String.eq(String.to_lower(v), "unlimited"), v), 2n)
    case 3n:
      opt.lim(name, lim.of(String.eq(String.to_lower(v), "unlimited"), v), 3n)
    case 4n:
      ROk{Opts{None{}, None{}, None{}, None{}, [v], False{}, None{}, None{}, None{}}}
    case 5n:
      +d = ungroup(v)
      opt.gate(name, u64(d), d, True{})
    case 6n:
      +d = ungroup(v)
      opt.gate(name, u64(d), d, False{})
    case 7n+u:
      +d = ungroup(v)
      opt.keep(keep_ok(d), d)

# The value of an option: given with `=`, or the next word
type Val is Data:
  # the value, and whether it took the next word
  VAt{value: String, took: Bool}
  VNone{}

def val.next.at(flag: Bool, w: String) -> Val:
  match flag:
    case True{}:
      VNone{}
    case False{}:
      VAt{w, True{}}

def val.next(ws: List<&2, String>) -> Val:
  match ws:
    case Nil{}:
      VNone{}
    case +w <> t:
      val.next.at(String.starts_with(w, "--"), w)

def val.of(eq: Bool, +tok: String, ws: List<&2, String>) -> Val:
  match eq:
    case True{}:
      VAt{after_eq(tok), False{}}
    case False{}:
      val.next(ws)

# the flag of a word: before its first `=`
def before_eq.at(b: Bool, c: Char, r: String) -> String:
  match b:
    case True{}:
      SNil{}
    case False{}:
      SCon{c, r}

def before_eq(s: String) -> String:
  match s:
    case SNil{}:
      SNil{}
    case SCon{+c, t}:
      before_eq.at(Char.is_eq(c, '='), c, before_eq(t))

# the flag's name: without `--autonomous-`, else without `--`
def name.dashes(b: Bool, raw: String) -> String:
  match b:
    case True{}:
      String.drop(raw, 2n)
    case False{}:
      raw

def name.of(b: Bool, +raw: String) -> String:
  match b:
    case True{}:
      String.drop(raw, 13n)
    case False{}:
      name.dashes(String.starts_with(raw, "--"), raw)

# One step of the options: the option of the word w (with the next word
# when it takes it), the reads of the words after w (r1) and after the
# next word (r2)
def step.took(empty: Bool, took: Bool, +raw: String, k: Nat, +name: String, x: String, r1: Read, r2: Read) -> Read:
  match empty:
    case True{}:
      RErr{auto_err("Missing value for ", raw)}
    case False{}:
      match took:
        case True{}:
          read.then(opt.value(k, name, x), r2)
        case False{}:
          read.then(opt.value(k, name, x), r1)

def step.val(v: Val, +raw: String, k: Nat, +name: String, r1: Read, r2: Read) -> Read:
  match v:
    case VNone{}:
      RErr{auto_err("Missing value for ", raw)}
    case VAt{+x, took}:
      step.took(String.is_empty(x), took, raw, k, name, x, r1, r2)

def step.known(m: Maybe<&2, Nat>, +w: String, +raw: String, +name: String, ws: List<&2, String>, r1: Read, r2: Read) -> Read:
  match m:
    case None{}:
      RErr{auto_err("Unknown autonomous budget flag: ", raw)}
    case Some{k}:
      step.val(val.of(String.contains(w, "="), w, ws), raw, k, name, r1, r2)

def step.flag(+w: String, ws: List<&2, String>, r1: Read, r2: Read) -> Read:
  +raw = before_eq(w)
  +name = name.of(String.starts_with(raw, "--autonomous-"), raw)
  step.known(index(name, flags(), 0n), w, raw, name, ws, r1, r2)

def step(dash: Bool, +w: String, ws: List<&2, String>, r1: Read, r2: Read) -> Read:
  match dash:
    case True{}:
      step.flag(w, ws, r1, r2)
    case False{}:
      RErr{auto_err("Unexpected autonomous argument: ", w)}

def reads.of(+w: String, +t: List<&2, String>, rr: Read & Read) -> Read & Read:
  (r1, r2) = rr
  +x = r1
  (step(String.starts_with(w, "--"), w, t, x, r2), x)

# the reads of ws and of ws without its first word
def reads(ws: List<&2, String>) -> Read & Read:
  match ws:
    case Nil{}:
      (ROk{opts.none()}, ROk{opts.none()})
    case +w <> +t:
      reads.of(w, t, reads(t))

# the options of the words ws
def options.fst(rr: Read & Read) -> Read:
  (r, s) = rr
  r

def options(ws: List<&2, String>) -> Read:
  options.fst(reads(ws))

def unl(m: Maybe<&2, Lim>) -> Maybe<&2, Lim>:
  match m:
    case None{}:
      Some{LUnl{}}
    case Some{l}:
      Some{l}

def conf.gates(cmds: List<&2, String>, gated: Bool, r: Maybe<&2, String>, s: Maybe<&2, String>) -> Maybe<&2, Gates>:
  match cmds:
    case Nil{}:
      match gated:
        case True{}:
          Some{Gates{None{}, r, s}}
        case False{}:
          None{}
    case c <> t:
      Some{Gates{Some{c <> t}, r, s}}

def conf.limits(named: Bool, c: Maybe<&2, Lim>, t: Maybe<&2, Lim>, k: Maybe<&2, Lim>, m: Maybe<&2, Lim>, g: Maybe<&2, Gates>, p: Maybe<&2, String>) -> Conf:
  match named:
    case True{}:
      Conf{unl(c), unl(t), unl(k), unl(m), g, p}
    case False{}:
      Conf{c, t, k, m, g, p}

def some(-A: Data, m: Maybe<&2, A>) -> Bool:
  match m:
    case None{}:
      False{}
    case Some{x}:
      True{}

# the options read, as `/autonomous on` takes them
def conf(o: Opts) -> Conf:
  match o:
    case Opts{+c, +t, +k, +m, g, d, r, s, p}:
      conf.limits(Bool.or(Bool.or(some(Lim, c), some(Lim, t)), Bool.or(some(Lim, k), some(Lim, m))), c, t, k, m, conf.gates(g, d, r, s), p)

def auto.on(r: Read) -> Auto:
  match r:
    case ROk{o}:
      AOn{conf(o)}
    case RErr{e}:
      AErr{e}

def auto.alone(ws: List<&2, String>, a: Auto) -> Auto:
  match ws:
    case Nil{}:
      a
    case w <> t:
      AErr{auto_err("Unexpected autonomous argument: ", w)}

def auto.kw(status: Bool, on: Bool, off: Bool, ws: List<&2, String>) -> Auto:
  match status:
    case True{}:
      auto.alone(ws, AStatus{})
    case False{}:
      match on:
        case True{}:
          auto.on(options(ws))
        case False{}:
          match off:
            case True{}:
              auto.alone(ws, AOff{})
            case False{}:
              AErr{auto_usage()}

def auto.first(+l: String, ws: List<&2, String>) -> Auto:
  auto.kw(String.eq(l, "status"), Bool.or(String.eq(l, "on"), Bool.or(String.eq(l, "enable"), String.eq(l, "enabled"))), Bool.or(String.eq(l, "off"), Bool.or(String.eq(l, "disable"), String.eq(l, "disabled"))), ws)

def auto.words(ws: List<&2, String>) -> Auto:
  match ws:
    case Nil{}:
      AStatus{}
    case w <> t:
      auto.first(String.to_lower(w), t)

# what `/autonomous <args>` asks
def auto(args: String) -> Auto:
  auto.words(words(args))
