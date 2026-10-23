# bridge_doc_commit: runs the models of bend/doc_commit.bend on an events
# file and prints what they did, line for line as the Rust bridge tests
# print the real code (crates/eukhe-docs/src/write/bridge.rs). Build it
# with
#
#   bend bridge/bridge_doc_commit.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   e O C F    one file of an edit, in payload order: an update (O 0) or
#              a move to a free name (1); changed since staging (C 1/0);
#              its fault: none (F 0), the directory sync fails (1), the
#              publish fails (2), the source removal fails (3, a move)
#   r          the session reads the file
#   x C        another writer writes content C to the file
#   d          another writer deletes the file
#   w C        the session writes content C to the file (the write tool)
#   f N C      a file named N (0..5) with content C
#   m S T      the session moves the file S to the name T (MV)
#   t I K H    an entry of the target's directory: id I; a temporary file
#              of the target (K 0), of another target (1), or another
#              file (2); held by a live writer (H 1/0)
#
# It prints, for each event in order,
#
#   w ok|refused       what a session write did
#   m ok|exists        what a move did, then
#   s N:C N:C ...      the files, by name, ascending
#
# and then, when the events had files of an edit,
#
#   r rejected|applied|partial   the reply of the edit
#   l I I ...          the files (by payload index) whose new content is on
#                      disk
#   p I I ...          the files the reply reports applied
#   w I I ...          the files the reply gives a warning
#
# and, when the events had entries of a directory,
#
#   x I I ...          the ids the sweep removes, in order

import Base
import ../bend/doc_commit.bend as Cm

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

def yes(n: Nat) -> Bool:
  match n:
    case 0n:
      False{}
    case 1n+m:
      True{}

def op(n: Nat) -> Cm.Op:
  match n:
    case 0n:
      Cm.Update{}
    case 1n+m:
      Cm.Moving{}

def fault(n: Nat) -> Cm.Fault:
  match n:
    case 0n:
      Cm.Clean{}
    case 1n+a:
      match a:
        case 0n:
          Cm.Sync{}
        case 1n+b:
          match b:
            case 0n:
              Cm.Publish{}
            case 1n+c:
              Cm.Remove{}

def sort(n: Nat) -> Cm.Sort:
  match n:
    case 0n:
      Cm.Own{}
    case 1n+a:
      match a:
        case 0n:
          Cm.Foreign{}
        case 1n+b:
          Cm.Plain{}

# Writing
# -------

def show.nats(ns: List<&2, Nat>) -> String:
  match ns:
    case Nil{}:
      ""
    case n <> rest:
      String.concat([" ", Nat.show(n), show.nats(rest)])

def show.ids(ns: List<&2, Cm.Temp>) -> String:
  match ns:
    case Nil{}:
      ""
    case n <> rest:
      match n:
        case Cm.Temp{i, k, h}:
          String.concat([" ", Nat.show(i), show.ids(rest)])

def show.one(+n: Nat, m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      ""
    case Some{c}:
      String.concat([" ", Nat.show(n), ":", Nat.show(c)])

# the files named n, n+1, ..., by name
def show.set(k: Nat, +n: Nat, +es: List<&2, Cm.Entry>) -> String:
  match k:
    case 0n:
      ""
    case 1n+more:
      String.concat([show.one(n, Cm.get(n, es)), show.set(more, 1n+n, es)])

def show.ok(b: Bool, yes: String, no: String) -> String:
  match b:
    case True{}:
      yes
    case False{}:
      no

def show.move(m: Cm.Mv) -> String & List<&2, Cm.Entry>:
  match m:
    case Cm.Mv{ok, +es}:
      (String.concat(["m ", show.ok(ok, "ok", "exists"), "\ns", show.set(6n, 0n, es), "\n"]), es)

def all_applied(rs: List<&2, Cm.Report>) -> Bool:
  match rs:
    case Nil{}:
      True{}
    case r <> rest:
      match r:
        case Cm.Applied{w}:
          all_applied(rest)
        case Cm.NotWritten{}:
          False{}

def warned(rs: List<&2, Cm.Report>, +n: Nat) -> List<&2, Nat>:
  match rs:
    case Nil{}:
      Nil{}
    case r <> rest:
      match r:
        case Cm.Applied{w}:
          match w:
            case True{}:
              n <> warned(rest, 1n+n)
            case False{}:
              warned(rest, 1n+n)
        case Cm.NotWritten{}:
          warned(rest, 1n+n)

# the reply and the landed files, as `r`, `l`, `p` and `w` lines
def show.reply(r: Cm.Reply, l: List<&2, Nat>) -> String:
  match r:
    case Cm.Rejected{}:
      String.concat(["r rejected\nl", show.nats(l), "\np\nw\n"])
    case Cm.Answered{+rs}:
      String.concat(["r ", show.ok(all_applied(rs), "applied", "partial"), "\nl", show.nats(l), "\np", show.nats(Cm.applied(rs, 0n)), "\nw", show.nats(warned(rs, 0n)), "\n"])

def show.edit(fs: List<&2, Cm.Doc>) -> String:
  match fs:
    case Nil{}:
      ""
    case f <> rest:
      +all = {f <> rest : List<&2, Cm.Doc>}
      show.reply(Cm.reply(all), Cm.landed(all))

def show.sweep(ns: List<&2, Cm.Temp>) -> String:
  match ns:
    case Nil{}:
      ""
    case n <> rest:
      String.concat(["x", show.ids(Cm.sweep(n <> rest)), "\n"])

# Running
# -------

# What the events built: the files of the edit (newest first), the disk
# and the seen versions of the written file, the files of the moves, the
# entries of the sweep (newest first), and the lines printed so far
# (newest first)
type St is Data:
  St{fs: List<&2, Cm.Doc>, disk: Maybe<&2, Nat>, seen: List<&2, Nat>, es: List<&2, Cm.Entry>, ts: List<&2, Cm.Temp>, out: List<&2, String>}

def read.put(d: Maybe<&2, Nat>, +s: List<&2, Nat>) -> List<&2, Nat>:
  match d:
    case None{}:
      s
    case Some{v}:
      Cm.saw(v, s)

def wrote(w: Cm.Wt, fs: List<&2, Cm.Doc>, es: List<&2, Cm.Entry>, ts: List<&2, Cm.Temp>, out: List<&2, String>) -> St:
  match w:
    case Cm.Wt{ok, d, s}:
      St{fs, d, s, es, ts, String.concat(["w ", show.ok(ok, "ok", "refused"), "\n"]) <> out}

def moved(m: String & List<&2, Cm.Entry>, fs: List<&2, Cm.Doc>, d: Maybe<&2, Nat>, s: List<&2, Nat>, ts: List<&2, Cm.Temp>, out: List<&2, String>) -> St:
  (text, es) = m
  St{fs, d, s, es, ts, text <> out}

def line(h: String, +ws: List<&2, String>, st: St) -> St:
  match h:
    case SCon{'e', r}:
      match st:
        case St{fs, d, s, es, ts, out}:
          St{Cm.Doc{op(arg(ws, 1n)), yes(arg(ws, 2n)), fault(arg(ws, 3n))} <> fs, d, s, es, ts, out}
    case SCon{'r', r}:
      match st:
        case St{fs, +d, s, es, ts, out}:
          St{fs, d, read.put(d, s), es, ts, out}
    case SCon{'x', r}:
      match st:
        case St{fs, d, s, es, ts, out}:
          St{fs, Some{arg(ws, 1n)}, s, es, ts, out}
    case SCon{'d', r}:
      match st:
        case St{fs, d, s, es, ts, out}:
          St{fs, None{}, s, es, ts, out}
    case SCon{'w', r}:
      match st:
        case St{fs, d, s, es, ts, out}:
          wrote(Cm.write(d, s, arg(ws, 1n)), fs, es, ts, out)
    case SCon{'f', r}:
      match st:
        case St{fs, d, s, es, ts, out}:
          St{fs, d, s, Cm.Entry{arg(ws, 1n), arg(ws, 2n)} <> es, ts, out}
    case SCon{'m', r}:
      match st:
        case St{fs, d, s, es, ts, out}:
          moved(show.move(Cm.move(arg(ws, 1n), arg(ws, 2n), es)), fs, d, s, ts, out)
    case SCon{'t', r}:
      match st:
        case St{fs, d, s, es, ts, out}:
          St{fs, d, s, es, Cm.Temp{arg(ws, 1n), sort(arg(ws, 2n)), yes(arg(ws, 3n))} <> ts, out}
    case r:
      st

def setup(ls: List<&2, String>, st: St) -> St:
  match ls:
    case Nil{}:
      st
    case l <> rest:
      +ws = String.split(l, ' ')
      setup(rest, line(tok.at(ws, 0n), ws, st))

def show(st: St) -> String:
  match st:
    case St{fs, d, s, es, ts, out}:
      String.concat([String.concat(List.reverse(&2, String, out)), show.edit(List.reverse(&2, Cm.Doc, fs)), show.sweep(List.reverse(&2, Cm.Temp, ts))])

def go(text: String) -> String:
  show(setup(String.lines(text), St{Nil{}, None{}, Nil{}, Nil{}, Nil{}, Nil{}}))

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
      IO.die(String, 2, "usage: bridge_doc_commit <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_doc_commit <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(text))
