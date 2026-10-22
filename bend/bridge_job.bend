# bridge_job: runs the job model (bend/job.bend) on an events file and
# prints what it did, line for line as the Rust bridge test prints the Rust
# jobs (crates/eukhe-core/src/durable/jobs/bridge.rs). Build it with
#
#   bend bend/bridge_job.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   c C          the job's output cap: Some{C} (`c -`: None, the opt-out);
#                the first line, before any job event
#   b B          the budget of the blocking wait on the job, in ticks; the
#                second line
#   o N          the job sees Out{N}
#   q C          the job sees Quit{C}
#   k            the job sees Kill{}
#   t            the job sees Tick{}
#   s I R        the job table gets the slot Slot{I, R} (R: 1 running, 0
#                ended)
#   r K ...      the job table is rewound to a tree that holds the jobs
#                K ... (none: the empty tree)
#
# After each job event (o, q, k, t) it prints one line:
#
#   j S e E w W  S: the job (`live K D`, `exited:C K D`, `killed K D`),
#                E: the ends the event reported (` exited:C`, ` killed`),
#                W: the wait's answer after the events so far (`none`
#                while it waits, `detached`, `exited:C`, `killed`)
#
# After each r it prints the slots, in order:
#
#   r I:R ...

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

# the ids of an `r` line, after its first word
def keep.of(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      tok.nat(w) <> keep.of(rest)

def keep.line(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      keep.of(rest)

def flag(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+m:
      True{}

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

def show.job(j: Jb.J) -> String:
  match j:
    case Jb.Live{k, d}:
      String.concat(["live ", Nat.show(k), " ", Nat.show(d)])
    case Jb.Ended{k, d, x}:
      String.concat([show.end(x), " ", Nat.show(k), " ", Nat.show(d)])

def show.ends(es: List<&2, Jb.End>) -> String:
  match es:
    case Nil{}:
      ""
    case e <> rest:
      String.concat([" ", show.end(e), show.ends(rest)])

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

def show.flag(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def show.slots(js: List<&2, Jb.Slot>) -> String:
  match js:
    case Nil{}:
      ""
    case +s <> rest:
      String.concat([" ", Nat.show(Jb.Slot.id(s)), ":", show.flag(Jb.Slot.running(s)), show.slots(rest)])

# Running
# -------

# the run so far: the cap, the budget, the job, the job events so far (in
# order), the job table, and the output of the last line
type St is Data:
  St{cap: Maybe<&2, Nat>, b: Nat, j: Jb.J, es: List<&2, Jb.JEv>, js: List<&2, Jb.Slot>, text: String}

def St.cap(s: St) -> Maybe<&2, Nat>:
  match s:
    case St{c, b, j, es, js, x}:
      c

def St.b(s: St) -> Nat:
  match s:
    case St{c, b, j, es, js, x}:
      b

def St.j(s: St) -> Jb.J:
  match s:
    case St{c, b, j, es, js, x}:
      j

def St.es(s: St) -> List<&2, Jb.JEv>:
  match s:
    case St{c, b, j, es, js, x}:
      es

def St.js(s: St) -> List<&2, Jb.Slot>:
  match s:
    case St{c, b, j, es, js, x}:
      js

def St.text(s: St) -> String:
  match s:
    case St{c, b, j, es, js, x}:
      x

# the job sees e: print the job, the ends e reported and the wait's answer
def see(+e: Jb.JEv, +s: St) -> St:
  +c = St.cap(s)
  +j = St.j(s)
  +n = Jb.step(c, j, e)
  +es = List.append(&2, Jb.JEv, St.es(s), [e])
  +text = String.concat(["j ", show.job(n), " e", show.ends(Jb.ends.of(j, e)), " w ", show.wait(Jb.wait(es, St.b(s))), "\n"])
  St{c, St.b(s), n, es, St.js(s), text}

# one line; h is its first word, ws all its words
def line(h: String, +ws: List<&2, String>, +s: St) -> St:
  match h:
    case SCon{'c', r}:
      St{cap.of(tok.at(ws, 1n)), St.b(s), St.j(s), St.es(s), St.js(s), ""}
    case SCon{'b', r}:
      St{St.cap(s), arg(ws, 1n), St.j(s), St.es(s), St.js(s), ""}
    case SCon{'o', r}:
      see(Jb.Out{arg(ws, 1n)}, s)
    case SCon{'q', r}:
      see(Jb.Quit{Jb.Code{0, U32.from_nat(arg(ws, 1n))}}, s)
    case SCon{'k', r}:
      see(Jb.Kill{}, s)
    case SCon{'t', r}:
      see(Jb.Tick{}, s)
    case SCon{'s', r}:
      +slot = {Jb.Slot{arg(ws, 1n), flag(arg(ws, 2n))} : Jb.Slot}
      St{St.cap(s), St.b(s), St.j(s), St.es(s), List.append(&2, Jb.Slot, St.js(s), [slot]), ""}
    case SCon{'r', r}:
      +js = Jb.rewind(St.js(s), keep.line(ws))
      St{St.cap(s), St.b(s), St.j(s), St.es(s), js, String.concat(["r", show.slots(js), "\n"])}
    case r:
      St{St.cap(s), St.b(s), St.j(s), St.es(s), St.js(s), ""}

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
    IO.write(go(String.lines(text), St{None{}, 0n, Jb.Live{0n, 0n}, Nil{}, Nil{}, ""}))
