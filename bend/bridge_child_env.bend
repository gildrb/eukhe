# bridge_child_env: runs the model of the environment of a child
# (bend/child_env.bend) on an events file and prints what it did, line for
# line as the Rust bridge test prints `child_env`
# (crates/eukhe-core/src/kernel/manager/startup/bridge.rs,
# `the_rust_child_env_equals_the_bend_model`). Build it with
#
#   bend bend/bridge_child_env.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line (names
# and values have no spaces):
#
#   r N N ...      the registry: the provider names
#   k N N ...      the keep list
#   b N V          a variable of the base
#   o N V          a variable of the overlay
#   q N            a name to look up, in order
#
# Then it prints, for each name to look up,
#
#   p N C R =V     C: 1 when N is a credential name, else 0; R: 1 when N
#   p N C R -      is a provider name, else 0; then the value of N in the
#                  child (=V), or - when the child has no N
#
# and last `n K`: the child has K variables.

import Base
import ./child_env.bend as Env

# Reading
# -------

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

# the words after the first
def rest(ws: List<&2, String>) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> more:
      more

type St is Data:
  St{reg: List<&2, String>, ks: List<&2, String>, base: List<&2, Env.Var>, over: List<&2, Env.Var>, qs: List<&2, String>}

# one line; h is its first word, ws all its words. Variables and names to
# look up are kept newest first.
def line(h: String, +ws: List<&2, String>, s: St) -> St:
  match h:
    case SCon{'r', t}:
      match s:
        case St{r, k, b, o, q}:
          St{rest(ws), k, b, o, q}
    case SCon{'k', t}:
      match s:
        case St{r, k, b, o, q}:
          St{r, rest(ws), b, o, q}
    case SCon{'b', t}:
      match s:
        case St{r, k, b, o, q}:
          St{r, k, Env.Var{tok.at(ws, 1n), tok.at(ws, 2n)} <> b, o, q}
    case SCon{'o', t}:
      match s:
        case St{r, k, b, o, q}:
          St{r, k, b, Env.Var{tok.at(ws, 1n), tok.at(ws, 2n)} <> o, q}
    case SCon{'q', t}:
      match s:
        case St{r, k, b, o, q}:
          St{r, k, b, o, tok.at(ws, 1n) <> q}
    case other:
      s

def setup(ls: List<&2, String>, s: St) -> St:
  match ls:
    case Nil{}:
      s
    case l <> more:
      +ws = String.split(l, ' ')
      setup(more, line(tok.at(ws, 0n), ws, s))

# Writing
# -------

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def found(hit: Bool, +v: Env.Var, +r: String) -> String:
  match hit:
    case True{}:
      match v:
        case Env.Var{n, x}:
          String.append("=", x)
    case False{}:
      r

# the value of the first variable of env named n (=V), or -
def lookup(+n: String, env: List<&2, Env.Var>) -> String:
  match env:
    case Nil{}:
      "-"
    case +v <> more:
      found(String.eq(Env.Var.name(v), n), v, lookup(n, more))

def probes(+reg: List<&2, String>, +env: List<&2, Env.Var>, qs: List<&2, String>) -> String:
  match qs:
    case Nil{}:
      ""
    case +n <> more:
      String.concat(["p ", n, " ", bit(Env.cred(reg, n)), " ", bit(Env.registered(reg, n)), " ", lookup(n, env), "\n", probes(reg, env, more)])

def run(s: St) -> String:
  match s:
    case St{+r, k, b, o, q}:
      +env = Env.child(r, k, List.reverse(&2, Env.Var, b), List.reverse(&2, Env.Var, o))
      String.concat([probes(r, env, List.reverse(&2, String, q)), "n ", Nat.show(List.length(&2, Env.Var, env)), "\n"])

def go(text: String) -> String:
  run(setup(String.lines(text), St{Nil{}, Nil{}, Nil{}, Nil{}, Nil{}}))

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
      IO.die(String, 2, "usage: bridge_child_env <events>")
    case prog <> more:
      match more:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_child_env <events>")
        case path <> others:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(text))
