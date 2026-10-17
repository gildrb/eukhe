# bridge_quirks: runs the quirks rulebook model (bend/infer.bend, section
# 1) on a scenario file and prints what it did, line for line as the Rust
# bridge test prints the Rust rulebook (eukhe_ai::quirks, driven by
# crates/eukhe-durable/src/harness/generation/infer_bridge.rs). Build it
# with
#
#   bend bend/bridge_quirks.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one line per step:
#
#   k N          the known directives are 0 .. N-1 (first line)
#   r L T D V    add a rule (after the rules so far): layer L (0 family,
#                1 model, 2 host), target T, directive D, value V
#   c            compile the rules so far
#   q F M H D    look up directive D for the query family F, model M,
#                host H
#
# It prints, for each `c` and `q` line:
#
#   c 1 | c 0    the rules compile | do not compile
#   q k V | q u  the answer is Known V | Unknown

import Base
import ./infer.bend as I

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

def tok.head(s: String) -> Char:
  match s:
    case SNil{}:
      ' '
    case SCon{c, t}:
      c

def lay.of(n: Nat) -> I.Lay:
  match n:
    case 0n:
      I.Fam{}
    case 1n+m:
      match m:
        case 0n:
          I.Mod{}
        case 1n+k:
          I.Host{}

def rule.of(+ws: List<&2, String>) -> I.Rule:
  I.Rule{lay.of(arg(ws, 1n)), arg(ws, 2n), arg(ws, 3n), arg(ws, 4n)}

def query.of(+ws: List<&2, String>) -> I.Query:
  I.Query{arg(ws, 1n), arg(ws, 2n), arg(ws, 3n)}

# the directives 0 .. n-1
def upto(n: Nat) -> List<&2, Nat>:
  match n:
    case 0n:
      Nil{}
    case 1n++m:
      m <> upto(m)

# Writing
# -------

def show.bool(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def show.ans(a: I.Ans) -> String:
  match a:
    case I.Known{v}:
      String.concat(["q k ", Nat.show(v), "\n"])
    case I.Unknown{}:
      "q u\n"

# Running
# -------

# what one line did: the known count and the rules after it, and its output
type Out is Data:
  Out{known: Nat, rs: List<&2, I.Rule>, text: String}

def Out.known(o: Out) -> Nat:
  match o:
    case Out{k, r, t}:
      k

def Out.rs(o: Out) -> List<&2, I.Rule>:
  match o:
    case Out{k, r, t}:
      r

def Out.text(o: Out) -> String:
  match o:
    case Out{k, r, t}:
      t

# one line; isk, isr, isq, isc say which kind its first word names
def line(isk: Bool, isr: Bool, isq: Bool, isc: Bool, +ws: List<&2, String>, +known: Nat, +rs: List<&2, I.Rule>) -> Out:
  match isk isr isq isc:
    case True{} isr isq isc:
      Out{arg(ws, 1n), rs, ""}
    case False{} True{} isq isc:
      Out{known, List.append(&2, I.Rule, rs, [rule.of(ws)]), ""}
    case False{} False{} True{} isc:
      Out{known, rs, show.ans(I.lookup(rs, query.of(ws), arg(ws, 4n)))}
    case False{} False{} False{} True{}:
      Out{known, rs, String.concat(["c ", show.bool(I.compiles(upto(known), rs)), "\n"])}
    case False{} False{} False{} False{}:
      Out{known, rs, ""}

def go(ls: List<&2, String>, +known: Nat, +rs: List<&2, I.Rule>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +h = tok.head(tok.at(ws, 0n))
      +o = line(Char.is_eq(h, 'k'), Char.is_eq(h, 'r'), Char.is_eq(h, 'q'), Char.is_eq(h, 'c'), ws, known, rs)
      String.append(Out.text(o), go(rest, Out.known(o), Out.rs(o)))

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
      IO.die(String, 2, "usage: bridge_quirks <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_quirks <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), 0n, Nil{}))
