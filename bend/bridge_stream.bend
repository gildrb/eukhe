# bridge_stream: runs the stream and cap model (bend/job.bend) on an
# events file and prints what it did, line for line as the Rust bridge
# tests print the Rust code (crates/eukhe-durable/src/harness/output/
# bridge.rs: the tool output bounder under a cap or the opt-out;
# crates/eukhe-durable/src/harness/tool/tests/bridge.rs: the storage
# writes of one real tool call). Build it with
#
#   bend bend/bridge_stream.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   c C          the bounder's cap: Some{C} (`c -`: None, the opt-out);
#                the first line of a bounder scenario
#   o N          the bounder takes N bytes: the job sees Out{N}
#   e            the output ends: the job sees Quit{0}
#   s            a tool call starts; the first line of a call scenario
#   d N          the call streams N bytes of its result: Delta{N}
#   w            the call warns: Warn{}
#   u N          the call records N tokens of usage: Use{N}
#   f            the call ends with its result: Final{}
#   x            the call is cancelled: Cancel{}
#
# After each o and e it prints the job (`live K D`, `exited:C K D`):
#
#   j S
#
# At the end of a call scenario it prints the call's journal, one record
# per line:
#
#   start
#   settle H B W U   H: `f` (finished) or `c` (cancelled); B: the result
#                    bytes, W: the warnings, U: the usage it carries

import Base
import ./job.bend as Jb

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

# the cap word of a `c` line
def cap.of(w: String) -> Maybe<&2, Nat>:
  match w:
    case SCon{'-', t}:
      None{}
    case w:
      Some{tok.nat(w)}

# Writing
# -------

def show.end(e: Jb.End) -> String:
  match e:
    case Jb.Exited{c}:
      String.append("exited:", Nat.show(c))
    case Jb.Killed{}:
      "killed"

def show.job(j: Jb.J) -> String:
  match j:
    case Jb.Live{k, d}:
      String.concat(["live ", Nat.show(k), " ", Nat.show(d)])
    case Jb.Ended{k, d, x}:
      String.concat([show.end(x), " ", Nat.show(k), " ", Nat.show(d)])

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

# the run so far: the cap, the job, whether a call started, the call's
# events so far (in order), and the output of the last line
type St is Data:
  St{cap: Maybe<&2, Nat>, j: Jb.J, call: Bool, es: List<&2, Jb.CEv>, text: String}

def St.cap(s: St) -> Maybe<&2, Nat>:
  match s:
    case St{c, j, k, es, x}:
      c

def St.j(s: St) -> Jb.J:
  match s:
    case St{c, j, k, es, x}:
      j

def St.call(s: St) -> Bool:
  match s:
    case St{c, j, k, es, x}:
      k

def St.es(s: St) -> List<&2, Jb.CEv>:
  match s:
    case St{c, j, k, es, x}:
      es

def St.text(s: St) -> String:
  match s:
    case St{c, j, k, es, x}:
      x

# the job sees e: print the job after it
def see(+e: Jb.JEv, +s: St) -> St:
  +c = St.cap(s)
  +n = Jb.step(c, St.j(s), e)
  St{c, n, St.call(s), St.es(s), String.concat(["j ", show.job(n), "\n"])}

# the call sees e: nothing to print until the end
def hear(+e: Jb.CEv, +s: St) -> St:
  St{St.cap(s), St.j(s), St.call(s), List.append(&2, Jb.CEv, St.es(s), [e]), ""}

# one line; h is its first word, ws all its words
def line(h: String, +ws: List<&2, String>, +s: St) -> St:
  match h:
    case SCon{'c', r}:
      St{cap.of(tok.at(ws, 1n)), St.j(s), St.call(s), St.es(s), ""}
    case SCon{'o', r}:
      see(Jb.Out{arg(ws, 1n)}, s)
    case SCon{'e', r}:
      see(Jb.Quit{0n}, s)
    case SCon{'s', r}:
      St{St.cap(s), St.j(s), True{}, St.es(s), ""}
    case SCon{'d', r}:
      hear(Jb.Delta{arg(ws, 1n)}, s)
    case SCon{'w', r}:
      hear(Jb.Warn{}, s)
    case SCon{'u', r}:
      hear(Jb.Use{arg(ws, 1n)}, s)
    case SCon{'f', r}:
      hear(Jb.Final{}, s)
    case SCon{'x', r}:
      hear(Jb.Cancel{}, s)
    case r:
      St{St.cap(s), St.j(s), St.call(s), St.es(s), ""}

# the journal of the call events es, when the scenario has a call
def journal.when(k: Bool, es: List<&2, Jb.CEv>) -> String:
  match k:
    case True{}:
      show.recs(Jb.journal(es))
    case False{}:
      ""

def journal.of(+s: St) -> String:
  journal.when(St.call(s), St.es(s))

def go(ls: List<&2, String>, +s: St) -> String:
  match ls:
    case Nil{}:
      journal.of(s)
    case l <> rest:
      +ws = String.split(l, ' ')
      +o = line(tok.at(ws, 0n), ws, s)
      String.append(St.text(o), go(rest, o))

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
    IO.write(go(String.lines(text), St{None{}, Jb.Live{0n, 0n}, False{}, Nil{}, ""}))
