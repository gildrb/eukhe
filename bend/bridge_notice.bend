# bridge_notice: runs the model of the restore notices a view shows
# (bend/notice.bend) on an events file and prints what it did, line for
# line as the Rust bridge test prints `RestoreNotices`
# (crates/eukhe-tui/src/restore_notices.rs,
# `the_restore_notices_run_as_their_model`). Build it with
#
#   bend bend/bridge_notice.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   r              a kernel restore stores a new notice
#   l              the newest stored notice arrives as a live event
#   c              the view attaches again and rebuilds its transcript
#
# After each event it prints
#
#   s C C ...      for each stored notice, in order, how many times it
#                  showed

import Base
import ./notice.bend as No

def show.counts(ns: List<&2, No.N>) -> String:
  match ns:
    case Nil{}:
      ""
    case n <> t:
      match n:
        case No.N{s, c}:
          String.concat([" ", Nat.show(c), show.counts(t)])

def show.st(ns: List<&2, No.N>) -> String:
  String.concat(["s", show.counts(ns), "\n"])

# the notices and the transcript
type Run is Data:
  Run{ns: List<&2, No.N>, out: String}

def op.then(+ns: List<&2, No.N>, out: String) -> Run:
  Run{ns, String.append(out, show.st(ns))}

def line(r: Run, h: String) -> Run:
  match r:
    case Run{ns, out}:
      match h:
        case SCon{'r', x}:
          op.then(No.step(ns, No.Restore{}), out)
        case SCon{'l', x}:
          op.then(No.step(ns, No.Live{}), out)
        case SCon{'c', x}:
          op.then(No.step(ns, No.Reconnect{}), out)
        case x:
          Run{ns, out}

def go(ls: List<&2, String>, r: Run) -> String:
  match ls:
    case Nil{}:
      match r:
        case Run{ns, out}:
          out
    case l <> rest:
      go(rest, line(r, l))

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
      IO.die(String, 2, "usage: bridge_notice <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_notice <events>")
        case path <> more:
          do IO<String>:
            f : File <- IO.try(File, File.open(path, "r"))
            m : File & Result<&1, &1, U32 & String, String> <- File.read(f, 1073741824)
            read.file(m)

def main() -> IO(Unit):
  do IO<Unit>:
    args : List<String> <- IO.args()
    text : String <- scenario(args)
    IO.write(go(String.lines(text), Run{Nil{}, ""}))
