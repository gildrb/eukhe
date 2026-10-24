# bridge_stream: runs the tool call journal of the stream model
# (bend/job.bend `journal`) on an events file and prints the journal, line
# for line as the Rust bridge test prints the storage writes of one real
# tool call (crates/eukhe-durable/src/harness/tool/tests/bridge.rs). What
# it ties is the interleaving: the commits async Rust makes while a call
# streams, which no entry of the compiled core can run. Build it with
#
#   bend bridge/bridge_stream.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   s            a tool call starts; the first line of a scenario
#   d N          the call streams N bytes of its result: Delta{N}
#   w            the call warns: Warn{}
#   u N          the call records N tokens of usage: Use{N}
#   f            the call ends with its result: Final{}
#   x            the call is cancelled: Cancel{}
#
# At the end of a scenario it prints the call's journal, one record per
# line:
#
#   start
#   settle H B W U   H: `f` (finished) or `c` (cancelled); B: the result
#                    bytes, W: the warnings, U: the usage it carries

import Base
import ../bend/job.bend as Jb

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

# Writing
# -------

def show.how(h: Jb.How) -> String:
  match h:
    case Jb.Finished{}:
      "f"
    case Jb.Cancelled{}:
      "c"

def show.rec(r: Jb.CRec) -> String:
  match r:
    case Jb.Start{}:
      "start\n"
    case Jb.Settle{h, b, w, u}:
      String.concat(["settle ", show.how(h), " ", Nat.show(b), " ", Nat.show(w), " ", Nat.show(u), "\n"])

def show.recs(rs: List<&2, Jb.CRec>) -> String:
  match rs:
    case Nil{}:
      ""
    case r <> rest:
      String.append(show.rec(r), show.recs(rest))

# Running
# -------

# the call's events so far, in order, after one line; h is its first word,
# ws all its words
def line(h: String, +ws: List<&2, String>, es: List<&2, Jb.CEv>) -> List<&2, Jb.CEv>:
  match h:
    case SCon{'d', r}:
      List.append(&2, Jb.CEv, es, [Jb.Delta{arg(ws, 1n)}])
    case SCon{'w', r}:
      List.append(&2, Jb.CEv, es, [Jb.Warn{}])
    case SCon{'u', r}:
      List.append(&2, Jb.CEv, es, [Jb.Use{arg(ws, 1n)}])
    case SCon{'f', r}:
      List.append(&2, Jb.CEv, es, [Jb.Final{}])
    case SCon{'x', r}:
      List.append(&2, Jb.CEv, es, [Jb.Cancel{}])
    case r:
      es

def go(ls: List<&2, String>, es: List<&2, Jb.CEv>) -> List<&2, Jb.CEv>:
  match ls:
    case Nil{}:
      es
    case l <> rest:
      +ws = String.split(l, ' ')
      go(rest, line(tok.at(ws, 0n), ws, es))

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
      IO.die(String, 2, "usage: bridge_stream <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_stream <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(show.recs(Jb.journal(go(String.lines(text), Nil{}))))
