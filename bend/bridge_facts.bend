# bridge_facts: runs the model of the model and provider facts
# (bend/facts.bend) on a scenario file and prints what it decided, line for
# line as the Rust bridge test prints the Rust code
# (crates/eukhe-core/src/durable/facts_bridge.rs). Build it with
#
#   bend bend/bridge_facts.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one event per line; a number
# or `-` (none) per word after the first:
#
#   r L T D V           a rule of the rulebook: layer L (0 family, 1 model,
#                       2 host), target T, directive D, value V
#   i A B C X G         the directive ids of adaptive_thinking,
#                       thinking_block_binding, prompt_caching,
#                       explicit_cache_breakpoints, google_thinking_level
#   d MI LO ME HI N     the default budgets and the answer room N
#   m F M H P           a model: its query (family F, model M, host H; a
#                       target no rule names for none) and its compat flag
#                       P (0 false, 1 true, 2 none); prints
#                       `m A B C0 C1 X G`: adaptive thinking, block binding,
#                       prompt caching without and with the user's force,
#                       explicit cache breakpoints, the Google thinking
#                       format (1: level)
#   g R MI LO ME HI L C a Google budget: R 1 with the rule MI..HI, 0
#                       without; level L (0 minimal .. 3 high); the user's
#                       budget C of the level; prints `g N` or `g -1`
#   f B MM L C          a fit: the caller's cap B, the model's cap MM, the
#                       level L, the user's budget C of the level; prints
#                       `f MAX BUDGET`
#   o B M               a budget B capped under the ceiling M; prints `o R`
#   x B                 an auxiliary cap over the budget B; prints `x CAP`
#   e L E0 .. E5        a Bedrock effort: level L (0 minimal .. 5 max), the
#                       map's entries (`-` missing, `n` null, a wire code);
#                       prints `e CODE`
#   s                   prints `s 1` when the default budgets are the old
#                       Bedrock table, else `s 0`
#   q                   clears the tier price rows
#   w M T K             a tier price row: model M (`-`: every model), tier
#                       T, multiplier K in hundredths
#   t M T               the multiplier of tier T for model M; prints `t K`
#                       or `t -` (no row)
#   h R I W             a 1h cache write: the row's multiplier R in
#                       hundredths (`-`: none), the input rate I and the
#                       cache write rate W (any one unit); prints `h RATE`
#                       in that unit

import Base
import ./infer.bend as If
import ./facts.bend as Fx

# Reading
# -------

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.head(s: String) -> Char:
  match s:
    case SNil{}:
      ' '
    case SCon{c, t}:
      c

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.opt.of(none: Bool, s: String) -> Maybe<&2, Nat>:
  match none:
    case True{}:
      None{}
    case False{}:
      Some{tok.nat(s)}

# word k: `-` is none, else a number
def tok.opt(+ws: List<&2, String>, k: Nat) -> Maybe<&2, Nat>:
  +s = tok.at(ws, k)
  tok.opt.of(Char.is_eq(tok.head(s), '-'), s)

def num(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

def lay(n: Nat) -> If.Lay:
  match n:
    case 0n:
      If.Fam{}
    case 1n+p:
      match p:
        case 0n:
          If.Mod{}
        case 1n+r:
          If.Host{}

def lv(n: Nat) -> Fx.Lv:
  match n:
    case 0n:
      Fx.Minimal{}
    case 1n+a:
      match a:
        case 0n:
          Fx.Low{}
        case 1n+b:
          match b:
            case 0n:
              Fx.Medium{}
            case 1n+c:
              Fx.High{}

def elv(n: Nat) -> Fx.ELv:
  match n:
    case 0n:
      Fx.EMinimal{}
    case 1n+a:
      match a:
        case 0n:
          Fx.ELow{}
        case 1n+b:
          match b:
            case 0n:
              Fx.EMedium{}
            case 1n+c:
              match c:
                case 0n:
                  Fx.EHigh{}
                case 1n+d:
                  match d:
                    case 0n:
                      Fx.EXhigh{}
                    case 1n+e:
                      Fx.EMax{}

def compat(n: Nat) -> Maybe<&2, Bool>:
  match n:
    case 0n:
      Some{False{}}
    case 1n+p:
      match p:
        case 0n:
          Some{True{}}
        case 1n+r:
          None{}

def ent.of(missing: Bool, null: Bool, s: String) -> Maybe<&2, Maybe<&2, Nat>>:
  match missing:
    case True{}:
      None{}
    case False{}:
      match null:
        case True{}:
          Some{None{}}
        case False{}:
          Some{Some{tok.nat(s)}}

# a thinking-level map entry at word k
def ent(+ws: List<&2, String>, k: Nat) -> Maybe<&2, Maybe<&2, Nat>>:
  +s = tok.at(ws, k)
  +c = tok.head(s)
  ent.of(Char.is_eq(c, '-'), Char.is_eq(c, 'n'), s)

# the user's budgets: c at level l, none elsewhere
def customs(l: Fx.Lv, c: Maybe<&2, Nat>) -> Fx.Customs:
  match l:
    case Fx.Minimal{}:
      Fx.Customs{c, None{}, None{}, None{}}
    case Fx.Low{}:
      Fx.Customs{None{}, c, None{}, None{}}
    case Fx.Medium{}:
      Fx.Customs{None{}, None{}, c, None{}}
    case Fx.High{}:
      Fx.Customs{None{}, None{}, None{}, c}

# Writing
# -------

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def opt.show(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "-"
    case Some{n}:
      Nat.show(n)

def gb.show(g: Fx.GB) -> String:
  match g:
    case Fx.Dynamic{}:
      "-1"
    case Fx.Tokens{n}:
      Nat.show(n)

# The state
# ---------

type St is Data:
  St{rules: List<&2, If.Rule>, ids: List<&2, Nat>, d: Fx.Budgets, a: Nat, prices: List<&2, Fx.PRow>}

def St.rules(s: St) -> List<&2, If.Rule>:
  match s:
    case St{r, i, d, a, p}:
      r

def St.ids(s: St) -> List<&2, Nat>:
  match s:
    case St{r, i, d, a, p}:
      i

def St.d(s: St) -> Fx.Budgets:
  match s:
    case St{r, i, d, a, p}:
      d

def St.a(s: St) -> Nat:
  match s:
    case St{r, i, d, a, p}:
      a

def St.prices(s: St) -> List<&2, Fx.PRow>:
  match s:
    case St{r, i, d, a, p}:
      p

def id(+s: St, k: Nat) -> Nat:
  Maybe.default(&2, Nat, List.get(&2, Nat, St.ids(s), k), 0n)

# the decisions of the model with query q and compat flag p
def model(+s: St, +q: If.Query, p: Maybe<&2, Bool>) -> String:
  +rs = St.rules(s)
  String.concat(["m ", bit(Fx.adaptive(p, If.lookup(rs, q, id(s, 0n)))), " ", bit(Fx.decide(rs, q, id(s, 1n), False{})), " ", bit(Fx.decide(rs, q, id(s, 2n), False{})), " ", bit(Fx.decide(rs, q, id(s, 2n), True{})), " ", bit(Fx.decide(rs, q, id(s, 3n), False{})), " ", bit(Fx.decide(rs, q, id(s, 4n), False{})), "\n"])

def google.rule(has: Bool, +ws: List<&2, String>) -> Maybe<&2, Fx.Budgets>:
  match has:
    case True{}:
      Some{Fx.Budgets{num(ws, 2n), num(ws, 3n), num(ws, 4n), num(ws, 5n)}}
    case False{}:
      None{}

def google(+ws: List<&2, String>) -> String:
  +l = lv(num(ws, 6n))
  String.concat(["g ", gb.show(Fx.gbudget(google.rule(Nat.is_eq(num(ws, 1n), 1n), ws), customs(l, tok.opt(ws, 7n)), l)), "\n"])

def fit(+s: St, +ws: List<&2, String>) -> String:
  +l = lv(num(ws, 3n))
  +f = Fx.fit(tok.opt(ws, 1n), num(ws, 2n), Fx.budget(customs(l, tok.opt(ws, 4n)), St.d(s), l), St.a(s))
  String.concat(["f ", Nat.show(Fx.Fit.max(f)), " ", Nat.show(Fx.Fit.budget(f)), "\n"])

def effort(+ws: List<&2, String>) -> String:
  +m = {Fx.EMap{ent(ws, 2n), ent(ws, 3n), ent(ws, 4n), ent(ws, 5n), ent(ws, 6n), ent(ws, 7n)} : Fx.EMap}
  String.concat(["e ", Nat.show(Fx.effort(m, elv(num(ws, 1n)))), "\n"])

def shipped(+b: Fx.Budgets) -> String:
  match b:
    case Fx.Budgets{+mi, +lo, +me, +hi}:
      +ok = Bool.and(Nat.is_eq(mi, 1024n), Bool.and(Nat.is_eq(lo, 2048n), Bool.and(Nat.is_eq(me, 8192n), Nat.is_eq(hi, 16384n))))
      String.concat(["s ", bit(ok), "\n"])

# what one line did: the state after it, and its output
type Out is Data:
  Out{s: St, text: String}

def Out.s(o: Out) -> St:
  match o:
    case Out{s, t}:
      s

def Out.text(o: Out) -> String:
  match o:
    case Out{s, t}:
      t

def rule(+ws: List<&2, String>) -> If.Rule:
  If.Rule{lay(num(ws, 1n)), num(ws, 2n), num(ws, 3n), num(ws, 4n)}

def line.h(hit: Bool, +c: Char, +ws: List<&2, String>, +s: St) -> Out:
  match hit:
    case True{}:
      Out{s, String.concat(["h ", Nat.show(Fx.rate_1h(tok.opt(ws, 1n), num(ws, 2n), num(ws, 3n))), "\n"])}
    case False{}:
      Out{s, ""}

def line.t(hit: Bool, +c: Char, +ws: List<&2, String>, +s: St) -> Out:
  match hit:
    case True{}:
      Out{s, String.concat(["t ", opt.show(Fx.price(St.prices(s), num(ws, 1n), num(ws, 2n))), "\n"])}
    case False{}:
      line.h(Char.is_eq(c, 'h'), c, ws, s)

def line.w(hit: Bool, +c: Char, +ws: List<&2, String>, +s: St) -> Out:
  match hit:
    case True{}:
      Out{St{St.rules(s), St.ids(s), St.d(s), St.a(s), List.append(&2, Fx.PRow, St.prices(s), [Fx.PRow{tok.opt(ws, 1n), num(ws, 2n), num(ws, 3n)}])}, ""}
    case False{}:
      line.t(Char.is_eq(c, 't'), c, ws, s)

def line.q(hit: Bool, +c: Char, +ws: List<&2, String>, +s: St) -> Out:
  match hit:
    case True{}:
      Out{St{St.rules(s), St.ids(s), St.d(s), St.a(s), Nil{}}, ""}
    case False{}:
      line.w(Char.is_eq(c, 'w'), c, ws, s)

def line.s(hit: Bool, +c: Char, +ws: List<&2, String>, +s: St) -> Out:
  match hit:
    case True{}:
      Out{s, shipped(St.d(s))}
    case False{}:
      line.q(Char.is_eq(c, 'q'), c, ws, s)

def line.e(hit: Bool, +c: Char, +ws: List<&2, String>, +s: St) -> Out:
  match hit:
    case True{}:
      Out{s, effort(ws)}
    case False{}:
      line.s(Char.is_eq(c, 's'), c, ws, s)

def line.x(hit: Bool, +c: Char, +ws: List<&2, String>, +s: St) -> Out:
  match hit:
    case True{}:
      Out{s, String.concat(["x ", Nat.show(Fx.aux_cap(num(ws, 1n), St.a(s))), "\n"])}
    case False{}:
      line.e(Char.is_eq(c, 'e'), c, ws, s)

def line.o(hit: Bool, +c: Char, +ws: List<&2, String>, +s: St) -> Out:
  match hit:
    case True{}:
      Out{s, String.concat(["o ", Nat.show(Fx.room(num(ws, 1n), num(ws, 2n), St.a(s))), "\n"])}
    case False{}:
      line.x(Char.is_eq(c, 'x'), c, ws, s)

def line.f(hit: Bool, +c: Char, +ws: List<&2, String>, +s: St) -> Out:
  match hit:
    case True{}:
      Out{s, fit(s, ws)}
    case False{}:
      line.o(Char.is_eq(c, 'o'), c, ws, s)

def line.g(hit: Bool, +c: Char, +ws: List<&2, String>, +s: St) -> Out:
  match hit:
    case True{}:
      Out{s, google(ws)}
    case False{}:
      line.f(Char.is_eq(c, 'f'), c, ws, s)

def line.m(hit: Bool, +c: Char, +ws: List<&2, String>, +s: St) -> Out:
  match hit:
    case True{}:
      Out{s, model(s, If.Query{num(ws, 1n), num(ws, 2n), num(ws, 3n)}, compat(num(ws, 4n)))}
    case False{}:
      line.g(Char.is_eq(c, 'g'), c, ws, s)

def line.d(hit: Bool, +c: Char, +ws: List<&2, String>, +s: St) -> Out:
  match hit:
    case True{}:
      Out{St{St.rules(s), St.ids(s), Fx.Budgets{num(ws, 1n), num(ws, 2n), num(ws, 3n), num(ws, 4n)}, num(ws, 5n), St.prices(s)}, ""}
    case False{}:
      line.m(Char.is_eq(c, 'm'), c, ws, s)

def line.i(hit: Bool, +c: Char, +ws: List<&2, String>, +s: St) -> Out:
  match hit:
    case True{}:
      Out{St{St.rules(s), [num(ws, 1n), num(ws, 2n), num(ws, 3n), num(ws, 4n), num(ws, 5n)], St.d(s), St.a(s), St.prices(s)}, ""}
    case False{}:
      line.d(Char.is_eq(c, 'd'), c, ws, s)

def line.r(hit: Bool, +c: Char, +ws: List<&2, String>, +s: St) -> Out:
  match hit:
    case True{}:
      Out{St{List.append(&2, If.Rule, St.rules(s), [rule(ws)]), St.ids(s), St.d(s), St.a(s), St.prices(s)}, ""}
    case False{}:
      line.i(Char.is_eq(c, 'i'), c, ws, s)

# one line, by its first word; any other line (the empty line after the
# last) prints nothing
def line(+c: Char, +ws: List<&2, String>, +s: St) -> Out:
  line.r(Char.is_eq(c, 'r'), c, ws, s)

def run(ls: List<&2, String>, +s: St) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +o = line(tok.head(tok.at(ws, 0n)), ws, s)
      String.append(Out.text(o), run(rest, Out.s(o)))

def read.done(r: Result<&1, &1, U32 & String, String>) -> String:
  match r:
    case Done{text}:
      text
    case Fail{e}:
      ""

def read.file(m: File & Result<&1, &1, U32 & String, String>) -> IO(String):
  (f, r) = m
  do IO<String>:
    Unit <- File.close(f)
    IO.pure(String, read.done(r))

def scenario(args: List<String>) -> IO(String):
  match args:
    case Nil{}:
      IO.die(String, 2, "usage: bridge_facts <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_facts <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(run(String.lines(text), St{Nil{}, Nil{}, Fx.Budgets{0n, 0n, 0n, 0n}, 0n, Nil{}}))
