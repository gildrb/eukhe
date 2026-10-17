# bridge_tiny: runs the tiny-model model (bend/tiny.bend) on a scenario
# file and prints what it did, line for line as the Rust bridge test
# prints the Rust code (crates/eukhe-tiny/src/bridge.rs). Build it with
#
#   bend bend/bridge_tiny.bend -o <out>
#
# and run `<out> <scenario>`. The first line names the part of the model:
#
#   p            the pick (`pick`); each line `K C1 .. CK U1 .. UM` (a
#                chain of K models, then the available ones) prints
#                `use M` (Use{M}) or `unavailable`
#   w            the worker of one model (`step`, `got`), from NoWorker;
#                one event a line:
#                  n P TAG  Need{P, TAG}
#                  g        Gone
#                after each it prints what the need got (`S` Started, `J`
#                Joined, `R` Replaced; `-` for none), then the worker:
#                ` w OWNER TAG` or ` none`

import Base
import ./tiny.bend as Tn

# Reading
# -------

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.head(s: String) -> Char:
  match s:
    case SNil{}:
      ' '
    case SCon{c, t}:
      c

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

def nats(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      tok.nat(w) <> nats(rest)

# the first k of xs
def take(k: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match k xs:
    case 0n xs:
      Nil{}
    case 1n+p Nil{}:
      Nil{}
    case 1n+p x <> rest:
      x <> take(p, rest)

# xs after the first k
def drop(k: Nat, xs: List<&2, Nat>) -> List<&2, Nat>:
  match k xs:
    case 0n xs:
      xs
    case 1n+p Nil{}:
      Nil{}
    case 1n+p x <> rest:
      drop(p, rest)

# the words after the first
def tail(ws: List<&2, String>) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      rest

# The pick
# --------

def pick.show(p: Tn.Pick) -> String:
  match p:
    case Tn.Use{m}:
      String.concat(["use ", Nat.show(m), "\n"])
    case Tn.Unavailable{}:
      "unavailable\n"

def pick.line(+ws: List<&2, String>) -> String:
  +k = arg(ws, 0n)
  +xs = nats(tail(ws))
  pick.show(Tn.pick(take(k, xs), drop(k, xs)))

def pick.go(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      String.append(pick.line(String.split(l, ' ')), pick.go(rest))

# The worker
# ----------

def ev.of(need: Bool, +ws: List<&2, String>) -> Tn.Ev:
  match need:
    case True{}:
      Tn.Need{arg(ws, 1n), arg(ws, 2n)}
    case False{}:
      Tn.Gone{}

def got.show(g: Tn.Got) -> String:
  match g:
    case Tn.Started{}:
      "S"
    case Tn.Joined{}:
      "J"
    case Tn.Replaced{}:
      "R"

def gots.show(gs: List<&2, Tn.Got>) -> String:
  match gs:
    case Nil{}:
      ""
    case g <> rest:
      String.append(got.show(g), gots.show(rest))

# `-` for no outcome
def gots.line(gs: List<&2, Tn.Got>) -> String:
  match gs:
    case Nil{}:
      "-"
    case g <> rest:
      gots.show(g <> rest)

def w.show(w: Tn.W) -> String:
  match w:
    case Tn.NoWorker{}:
      " none\n"
    case Tn.Worker{o, t}:
      String.concat([" w ", Nat.show(o), " ", Nat.show(t), "\n"])

def w.go(ls: List<&2, String>, +w: Tn.W) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      +e = ev.of(Char.is_eq(tok.head(tok.at(ws, 0n)), 'n'), ws)
      +next = Tn.step(w, e)
      String.concat([gots.line(Tn.got(w, e)), w.show(next), w.go(rest, next)])

# Running
# -------

def run.part(pick: Bool, +rest: List<&2, String>) -> String:
  match pick:
    case True{}:
      pick.go(rest)
    case False{}:
      w.go(rest, Tn.NoWorker{})

def run(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      run.part(Char.is_eq(tok.head(l), 'p'), rest)

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
      IO.die(String, 2, "usage: bridge_tiny <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_tiny <scenario>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(run(String.lines(text)))
