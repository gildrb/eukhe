# bridge_job: runs the model of a blocking wait on a job (bend/job.bend
# `wait`) on an events file and prints its answer after each event, line
# for line as the Rust bridge test prints the Rust wait (`wait_until`,
# crates/eukhe-core/src/durable/jobs/bridge.rs). The compiled core decides
# each poll of the Rust wait (`poll`, laws/job.bend); the bridge ties the
# interleaving: the timer against the job's end. Build it with
#
#   bend bridge/bridge_job.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   b B          the budget of the wait, in ticks; the first line
#   o N          the job sees Out{N}
#   q C          the job sees Quit{C}
#   k            the job sees Kill{}
#   t            the job sees Tick{}
#
# After each job event (o, q, k, t) it prints the wait's answer after the
# events so far:
#
#   w W          W: `none` while it waits, `detached`, `exited:C`, `killed`

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

# the bridge's exit codes are 0..2: the low word is the code
def show.end(e: Jb.End) -> String:
  match e:
    case Jb.Exited{c}:
      match c:
        case Jb.Code{hi, lo}:
          String.append("exited:", U32.show(lo))
    case Jb.Killed{}:
      "killed"

def show.answer(w: Jb.Wait) -> String:
  match w:
    case Jb.Settled{e}:
      show.end(e)
    case Jb.Detached{}:
      "detached"

def show.wait(w: Maybe<&2, Jb.Wait>) -> String:
  match w:
    case None{}:
      "none"
    case Some{a}:
      show.answer(a)

# Running
# -------

# the run so far: the budget, the job events so far (in order), and the
# output of the last line
type St is Data:
  St{b: Nat, es: List<&2, Jb.JEv>, text: String}

def St.b(s: St) -> Nat:
  match s:
    case St{b, es, x}:
      b

def St.es(s: St) -> List<&2, Jb.JEv>:
  match s:
    case St{b, es, x}:
      es

def St.text(s: St) -> String:
  match s:
    case St{b, es, x}:
      x

# the job sees e: print the wait's answer
def see(+e: Jb.JEv, +s: St) -> St:
  +es = List.append(&2, Jb.JEv, St.es(s), [e])
  St{St.b(s), es, String.concat(["w ", show.wait(Jb.wait(es, St.b(s))), "\n"])}

# one line; h is its first word, ws all its words
def line(h: String, +ws: List<&2, String>, +s: St) -> St:
  match h:
    case SCon{'b', r}:
      St{arg(ws, 1n), St.es(s), ""}
    case SCon{'o', r}:
      see(Jb.Out{arg(ws, 1n)}, s)
    case SCon{'q', r}:
      see(Jb.Quit{Jb.Code{0, U32.from_nat(arg(ws, 1n))}}, s)
    case SCon{'k', r}:
      see(Jb.Kill{}, s)
    case SCon{'t', r}:
      see(Jb.Tick{}, s)
    case r:
      St{St.b(s), St.es(s), ""}

def go(ls: List<&2, String>, +s: St) -> String:
  match ls:
    case Nil{}:
      ""
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
      IO.die(String, 2, "usage: bridge_job <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_job <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), St{0n, Nil{}, ""}))
