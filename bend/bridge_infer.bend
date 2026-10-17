# bridge_infer: runs the inference layer model (bend/infer.bend, sections
# 2 to 5) on a scenario file and prints what it did, line for line as the
# Rust bridge test prints the Rust units
# (crates/eukhe-durable/src/harness/generation/infer_bridge.rs). Build it
# with
#
#   bend bend/bridge_infer.bend -o <out>
#
# and run `<out> <scenario>`. A scenario has one problem per line:
#
#   f R S F C...   a forced call: R retries, S the provider supports the
#                  native flag (1/0), F it is free (1/0), C the replies in
#                  order (1: the model called the tool)
#   s C P...       the strict budget: cap C, one tool per P (its
#                  priority); tool i is the i-th, from 0
#   g K X...       the repetition guard: run K, X the chunk ids in order
#   t T L X...     early compaction: X the context sizes per turn; T the
#                  threshold, L the limit
#
# It prints one line per problem:
#
#   f B... called|missed   each attempt's native flag (1/0), the outcome
#   s SL...                per tool, in order: how many times it is strict
#                          (S) and loose (L)
#   g whole | g cut N      the stream went to its end | was cut after N
#                          chunks
#   t A B                  the first turn at or above T, the first turn at
#                          or above L + 1 (`none`: no such turn)

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

def flag(+ws: List<&2, String>, k: Nat) -> Bool:
  Nat.is_eq(arg(ws, k), 1n)

def tok.head(s: String) -> Char:
  match s:
    case SNil{}:
      ' '
    case SCon{c, t}:
      c

def nats(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      tok.nat(w) <> nats(rest)

def bools(ws: List<&2, String>) -> List<&2, Bool>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      Nat.is_eq(tok.nat(w), 1n) <> bools(rest)

# the tools of priorities ws, tool i first
def tools(ws: List<&2, String>, +i: Nat) -> List<&2, I.Tool>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      I.Tool{i, tok.nat(w)} <> tools(rest, 1n+i)

def rest(+ws: List<&2, String>, k: Nat) -> List<&2, String>:
  List.drop(&2, String, ws, k)

# Writing
# -------

def show.bool(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def show.tries(ts: List<&2, I.Try>) -> String:
  match ts:
    case Nil{}:
      ""
    case t <> more:
      String.concat([" ", show.bool(I.Try.flag(t)), show.tries(more)])

def show.forced(o: I.Forced) -> String:
  match o:
    case I.Called{}:
      " called"
    case I.Missed{}:
      " missed"

def show.force(p: List<&2, I.Try> & I.Forced) -> String:
  (ts, o) = p
  String.concat(["f", show.tries(ts), show.forced(o), "\n"])

# per tool i .. i+k-1: its count in st and in lo
def marks(+st: List<&2, I.Tool>, +lo: List<&2, I.Tool>, k: Nat, +i: Nat) -> String:
  match k:
    case 0n:
      ""
    case 1n+m:
      String.concat([" ", Nat.show(I.count(st, i)), Nat.show(I.count(lo, i)), marks(st, lo, m, 1n+i)])

def show.strict(p: List<&2, I.Tool> & List<&2, I.Tool>, n: Nat) -> String:
  (st, lo) = p
  String.concat(["s", marks(st, lo, n, 0n), "\n"])

def show.cut(c: I.Cut) -> String:
  match c:
    case I.Whole{}:
      "g whole\n"
    case I.CutAt{n}:
      String.concat(["g cut ", Nat.show(n), "\n"])

def show.at(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "none"
    case Some{i}:
      Nat.show(i)

def show.first(+xs: List<&2, Nat>, +t: Nat, +lim: Nat) -> String:
  String.concat(["t ", show.at(I.first_at(xs, t, 0n)), " ", show.at(I.first_at(xs, 1n+lim, 0n)), "\n"])

# Running
# -------

# one line; isf, iss, isg, ist say which kind its first word names
def line(isf: Bool, iss: Bool, isg: Bool, ist: Bool, +ws: List<&2, String>) -> String:
  match isf iss isg ist:
    case True{} iss isg ist:
      show.force(I.force(arg(ws, 1n), bools(rest(ws, 4n)), flag(ws, 2n), flag(ws, 3n)))
    case False{} True{} isg ist:
      show.strict(I.strict(arg(ws, 1n), tools(rest(ws, 2n), 0n)), List.length(&2, String, rest(ws, 2n)))
    case False{} False{} True{} ist:
      show.cut(I.guard(nats(rest(ws, 2n)), arg(ws, 1n)))
    case False{} False{} False{} True{}:
      show.first(nats(rest(ws, 3n)), arg(ws, 1n), arg(ws, 2n))
    case False{} False{} False{} False{}:
      ""

def go(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> more:
      +ws = String.split(l, ' ')
      +h = tok.head(tok.at(ws, 0n))
      String.append(line(Char.is_eq(h, 'f'), Char.is_eq(h, 's'), Char.is_eq(h, 'g'), Char.is_eq(h, 't'), ws), go(more))

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
      IO.die(String, 2, "usage: bridge_infer <scenario>")
    case prog <> more:
      match more:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_infer <scenario>")
        case path <> others:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text)))
