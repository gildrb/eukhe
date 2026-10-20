# bridge_doc_search: runs the models of bend/doc_search.bend on an events
# file and prints what they did, line for line as the Rust bridge tests
# print the real code (crates/eukhe-docs/src/grep/bridge_accounts.rs,
# crates/eukhe-docs/src/glob/bridge.rs). Build it with
#
#   bend bend/bridge_doc_search.bend -o <out>
#
# and run `<out> <events>`. An events file has one event per line:
#
#   g P S K R      a grep: P matches a file at most, skip S matching files,
#                  K files a page, R matches in all
#   t I H B        a text file I with H matches, over the size limit (B 1)
#                  or not (B 0)
#   s I W          an entry I the search skips: W 0 binary, 1 does not
#                  open, 2 excluded directory, 3 symlink, 4 walk error
#   o S K          a glob: skip S paths, limit K
#   p I M          a path I changed at time M
#
# The walk meets the entries in the order of the events. A grep prints
#
#   c N S P U B R X L E A   the count of each class: no match, shown, paged
#                           out, not searched, binary, does not open,
#                           excluded, symlink, walk error; and A searched
#                           only in part
#   n B R X L E A U         1 when the notice of that class is there:
#                           binary, does not open, excluded, symlink,
#                           walk error, searched in part, not searched
#   x I I ...               the files with a notice that matches were cut
#   f I I ...               the files of the page
#   r C                     the continuation (`r -`: none), then, when
#                           there is one, the `f` line of its page
#
# A glob prints an `f` line and an `r` line for its page and for the page
# of each continuation it gives.

import Base
import ./doc_search.bend as Sr

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

def reason(n: Nat) -> Sr.Reason:
  match n:
    case 0n:
      Sr.Binary{}
    case 1n+a:
      match a:
        case 0n:
          Sr.Unreadable{}
        case 1n+b:
          match b:
            case 0n:
              Sr.Excluded{}
            case 1n+c:
              match c:
                case 0n:
                  Sr.Link{}
                case 1n+d:
                  Sr.Broken{}

# What the events set up, each list newest first: the grep (P S K R), the
# entries, the glob (S K) and the paths
type St is Data:
  St{grep: List<&2, Nat>, ents: List<&2, Sr.Ent>, glob: List<&2, Nat>, paths: List<&2, Sr.Path>}

def line(h: String, +ws: List<&2, String>, s: St) -> St:
  match h:
    case SCon{'g', r}:
      match s:
        case St{g, es, o, ps}:
          St{[arg(ws, 1n), arg(ws, 2n), arg(ws, 3n), arg(ws, 4n)], es, o, ps}
    case SCon{'t', r}:
      match s:
        case St{g, es, o, ps}:
          St{g, Sr.Ent{arg(ws, 1n), Sr.Text{arg(ws, 2n), yes(arg(ws, 3n))}} <> es, o, ps}
    case SCon{'s', r}:
      match s:
        case St{g, es, o, ps}:
          St{g, Sr.Ent{arg(ws, 1n), Sr.Skip{reason(arg(ws, 2n))}} <> es, o, ps}
    case SCon{'o', r}:
      match s:
        case St{g, es, o, ps}:
          St{g, es, [arg(ws, 1n), arg(ws, 2n)], ps}
    case SCon{'p', r}:
      match s:
        case St{g, es, o, ps}:
          St{g, es, o, Sr.Path{arg(ws, 1n), arg(ws, 2n)} <> ps}
    case r:
      s

def setup(ls: List<&2, String>, s: St) -> St:
  match ls:
    case Nil{}:
      s
    case l <> rest:
      +ws = String.split(l, ' ')
      setup(rest, line(tok.at(ws, 0n), ws, s))

# Writing
# -------

def show.nats(ns: List<&2, Nat>) -> String:
  match ns:
    case Nil{}:
      ""
    case n <> rest:
      String.concat([" ", Nat.show(n), show.nats(rest)])

def bit(b: Bool) -> Nat:
  match b:
    case True{}:
      1n
    case False{}:
      0n

def show.count(c: Sr.Count) -> String:
  match c:
    case Sr.Count{a, b, d, e, f, g, h, i, j, pa}:
      String.concat(["c", show.nats([a, b, d, e, f, g, h, i, j, pa]), "\n"])

def show.noted(+os: List<&2, Sr.Out>, ns: List<&2, Sr.Note>) -> List<&2, Nat>:
  match ns:
    case Nil{}:
      Nil{}
    case n <> rest:
      bit(Sr.noted(n, os)) <> show.noted(os, rest)

def show.notes(+os: List<&2, Sr.Out>) -> String:
  +ns = {[Sr.NSkip{Sr.Binary{}}, Sr.NSkip{Sr.Unreadable{}}, Sr.NSkip{Sr.Excluded{}}, Sr.NSkip{Sr.Link{}}, Sr.NSkip{Sr.Broken{}}, Sr.NPartial{}, Sr.NUnsearched{}] : List<&2, Sr.Note>}
  String.concat(["n", show.nats(show.noted(os, ns)), "\n"])

def show.page(+ps: List<&2, Nat>, +s: Nat, +k: Nat) -> String:
  String.concat(["f", show.nats(Sr.page(ps, s, k)), "\n"])

def show.next(+ps: List<&2, Nat>, +k: Nat, m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "r -\n"
    case Some{+c}:
      String.concat(["r ", Nat.show(c), "\n", show.page(ps, c, k)])

def show.grep.go(+p: Nat, +s: Nat, +k: Nat, +rem: Nat, +es: List<&2, Sr.Ent>) -> String:
  +os = Sr.run(es, p, s, k, rem, 0n)
  +hs = Sr.hits(os)
  String.concat([show.count(Sr.account(os)), show.notes(os), "x", show.nats(Sr.cuts(os)), "\n", show.page(hs, s, k), show.next(hs, k, Sr.next(hs, s, k))])

def show.grep(g: List<&2, Nat>, +es: List<&2, Sr.Ent>) -> String:
  match g:
    case Nil{}:
      ""
    case p <> r1:
      match r1:
        case Nil{}:
          ""
        case s <> r2:
          match r2:
            case Nil{}:
              ""
            case k <> r3:
              match r3:
                case Nil{}:
                  ""
                case rem <> r4:
                  show.grep.go(p, s, k, rem, es)

def show.r(m: Maybe<&2, Nat>) -> String:
  match m:
    case None{}:
      "r -\n"
    case Some{c}:
      String.concat(["r ", Nat.show(c), "\n"])

# the page at each skip of m: the first, then each continuation, at most
# `fuel` pages
def show.glob.go(fuel: Nat, +ps: List<&2, Nat>, +k: Nat, m: Maybe<&2, Nat>) -> String:
  match fuel:
    case 0n:
      ""
    case 1n+f:
      match m:
        case None{}:
          ""
        case Some{+s}:
          +n = Sr.next(ps, s, k)
          String.concat([show.page(ps, s, k), show.r(n), show.glob.go(f, ps, k, n)])

def show.glob(o: List<&2, Nat>, +ps: List<&2, Sr.Path>) -> String:
  match o:
    case Nil{}:
      ""
    case s <> r1:
      match r1:
        case Nil{}:
          ""
        case k <> r2:
          +ids = Sr.ranked(ps)
          show.glob.go(1n+List.length(&2, Nat, ids), ids, Sr.glob.size(k), Some{s})

def show(s: St) -> String:
  match s:
    case St{g, es, o, ps}:
      String.concat([show.grep(g, List.reverse(&2, Sr.Ent, es)), show.glob(o, List.reverse(&2, Sr.Path, ps))])

def go(text: String) -> String:
  show(setup(String.lines(text), St{Nil{}, Nil{}, Nil{}, Nil{}}))

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
      IO.die(String, 2, "usage: bridge_doc_search <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_doc_search <events>")
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
