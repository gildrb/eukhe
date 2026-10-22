# bridge_doc_seen: runs the model of bend/doc_seen.bend on an events file
# and prints what it did, line for line as the Rust bridge test prints
# the real tools (crates/eukhe-core/src/durable/documents/bridge.rs,
# `edits_apply_only_on_seen_lines_as_their_model`). Build it with
#
#   bend bend/bridge_doc_seen.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line, after
# one bounded read of a long file:
#
#   v N S        the row of line N is in the text the read returned
#                (S 1) or not (S 0)
#   e A B        an edit that replaces the lines A to B (its anchors)
#
# For each edit it prints
#
#   ok           the edit applied
#   unseen       the edit was rejected: an anchor is not seen

import Base
import ./doc_seen.bend as Ds

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

# the anchors of the n lines from a on (the bridge's file has short
# lines, and its edits stay inside it: each anchor is a line that the
# rejection shows whole)
def lines(n: Nat, +a: Nat) -> List<&2, Ds.At>:
  match n:
    case 0n:
      Nil{}
    case 1n+m:
      Ds.At{a, Some{0n}} <> lines(m, 1n+a)

# the seen lines, and what the edits printed, newest first
type St is Data:
  St{seen: List<&2, Ds.Iv>, out: List<&2, String>}

def said(s: Ds.Step, out: List<&2, String>) -> St:
  match s:
    case Ds.Step{applied, seen}:
      match applied:
        case True{}:
          St{seen, "ok" <> out}
        case False{}:
          St{seen, "unseen" <> out}

def line(h: String, +ws: List<&2, String>, s: St) -> St:
  match h:
    case SCon{'v', r}:
      match s:
        case St{seen, out}:
          St{Ds.show(arg(ws, 1n), seen, yes(arg(ws, 2n))), out}
    case SCon{'e', r}:
      match s:
        case St{seen, out}:
          +a = arg(ws, 1n)
          said(Ds.edit(seen, lines(1n+Nat.sub(arg(ws, 2n), a), a)), out)
    case r:
      s

def run(ls: List<&2, String>, s: St) -> St:
  match ls:
    case Nil{}:
      s
    case l <> rest:
      +ws = String.split(l, ' ')
      run(rest, line(tok.at(ws, 0n), ws, s))

# Writing
# -------

def show.out(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      String.concat([l, "\n", show.out(rest)])

def show(s: St) -> String:
  match s:
    case St{seen, out}:
      show.out(List.reverse(&2, String, out))

def go(text: String) -> String:
  show(run(String.lines(text), St{Nil{}, Nil{}}))

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
      IO.die(String, 2, "usage: bridge_doc_seen <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_doc_seen <events>")
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
