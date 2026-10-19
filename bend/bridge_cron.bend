# bridge_cron: runs the cron model (bend/cron.bend) on an events file and
# prints the jobs file after each event, line for line as the Rust bridge
# test prints the Rust stores (crates/eukhe-core/src/cron/store/bridge.rs).
# Build it with
#
#   bend bend/bridge_cron.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line (P a
# process, I a job id, D a number of minutes, T the bytes of a record):
#
#   c P o D      P makes a one-shot job that runs in 1+D minutes
#   c P e D      P makes a job that runs each 1+D minutes
#   k P          P claims the due jobs
#   v P          P recovers claims
#   f P I w      P finishes its run of job I: good (w), failed (l),
#                skipped (s)
#   a P          the pass of P unwinds: its runs end
#   x P          P dies
#   n P I        the user cancels job I (through P)
#   u P I        the user resumes job I (through P)
#   t D          D minutes pass
#   r T          another writer adds a job record this build cannot read
#   q T          another writer adds a claim record this build cannot read
#   z T          the file becomes corrupt (its bytes: T)
#
# After each event it prints one line:
#
#   b B | J ... | R ... | Q ... | A ...
#
# B: the corrupt file's bytes, or `-`. J: each job, in id order, as
# `I:S:N:K:C` (S: a active, p paused, f finished, c cancelled; N: its next
# run or `-`; K: its failures in a row; C: its claim `O@P`, or `-`). R and
# Q: the records this build cannot read, in file order. A: the corrupt
# files moved aside, the newest first.

import Base
import ./cron.bend as Cr

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

def sched.of(w: String, +d: Nat) -> Cr.Sched:
  match w:
    case SCon{'o', t}:
      Cr.Once{d}
    case w:
      Cr.Every{d}

def out.of(w: String) -> Cr.Out:
  match w:
    case SCon{'w', t}:
      Cr.Win{}
    case SCon{'l', t}:
      Cr.Loss{}
    case w:
      Cr.Skip{}

# the event of one line; None: no event
def event(h: String, +ws: List<&2, String>) -> Maybe<&2, Cr.Ev>:
  match h:
    case SCon{'c', r}:
      Some{Cr.Create{arg(ws, 1n), sched.of(tok.at(ws, 2n), arg(ws, 3n))}}
    case SCon{'k', r}:
      Some{Cr.Take{arg(ws, 1n)}}
    case SCon{'v', r}:
      Some{Cr.Recover{arg(ws, 1n)}}
    case SCon{'f', r}:
      Some{Cr.Finish{arg(ws, 1n), arg(ws, 2n), out.of(tok.at(ws, 3n))}}
    case SCon{'a', r}:
      Some{Cr.Abort{arg(ws, 1n)}}
    case SCon{'x', r}:
      Some{Cr.Die{arg(ws, 1n)}}
    case SCon{'n', r}:
      Some{Cr.Cancel{arg(ws, 1n), arg(ws, 2n)}}
    case SCon{'u', r}:
      Some{Cr.Resume{arg(ws, 1n), arg(ws, 2n)}}
    case SCon{'t', r}:
      Some{Cr.Tick{arg(ws, 1n)}}
    case SCon{'r', r}:
      Some{Cr.RawJob{arg(ws, 1n)}}
    case SCon{'q', r}:
      Some{Cr.RawClaim{arg(ws, 1n)}}
    case SCon{'z', r}:
      Some{Cr.Corrupt{arg(ws, 1n)}}
    case r:
      None{}

# Writing
# -------

def show.status(st: Cr.Status) -> String:
  match st:
    case Cr.Active{}:
      "a"
    case Cr.Paused{}:
      "p"
    case Cr.Finished{}:
      "f"
    case Cr.Cancelled{}:
      "c"

def show.opt(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "-"
    case Some{n}:
      Nat.show(n)

def show.claim(m: Maybe<&2, Cr.Claim>) -> String:
  match m:
    case None{}:
      "-"
    case Some{x}:
      match x:
        case Cr.Claim{o, p}:
          String.concat([Nat.show(o), "@", Nat.show(p)])

def show.job(j: Cr.Job) -> String:
  match j:
    case Cr.Job{i, s, st, nx, k, cl, rs, ss, h}:
      String.concat([" ", Nat.show(i), ":", show.status(st), ":", show.opt(nx), ":", Nat.show(k), ":", show.claim(cl)])

def show.jobs(rs: List<&2, Cr.Rec>) -> String:
  match rs:
    case Nil{}:
      ""
    case r <> t:
      match r:
        case Cr.Known{j}:
          String.append(show.job(j), show.jobs(t))
        case Cr.Raw{x}:
          show.jobs(t)

def show.raws(rs: List<&2, Cr.Rec>) -> String:
  match rs:
    case Nil{}:
      ""
    case r <> t:
      match r:
        case Cr.Known{j}:
          show.raws(t)
        case Cr.Raw{x}:
          String.concat([" ", Nat.show(x), show.raws(t)])

def show.nats(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> t:
      String.concat([" ", Nat.show(x), show.nats(t)])

def show(s: Cr.S) -> String:
  match s:
    case Cr.S{b, +rs, rd, dead, c, n, a}:
      String.concat(["b ", show.opt(b), " |", show.jobs(rs), " |", show.raws(rs), " |", show.nats(rd), " |", show.nats(a), "\n"])

# Running
# -------

# the state after a line and what it prints
type Seen is Data:
  Seen{s: Cr.S, text: String}

def Seen.s(x: Seen) -> Cr.S:
  match x:
    case Seen{s, t}:
      s

def Seen.text(x: Seen) -> String:
  match x:
    case Seen{s, t}:
      t

def line(m: Maybe<&2, Cr.Ev>, +s: Cr.S) -> Seen:
  match m:
    case None{}:
      Seen{s, ""}
    case Some{e}:
      +o = Cr.step(s, e)
      Seen{o, show(o)}

def go(ls: List<&2, String>, +s: Cr.S) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +o = line(event(tok.at(ws, 0n), ws), s)
      String.append(Seen.text(o), go(rest, Seen.s(o)))

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
      IO.die(String, 2, "usage: bridge_cron <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_cron <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), Cr.S.empty()))
