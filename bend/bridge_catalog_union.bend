# bridge_catalog_union: runs the model of the built-in catalog's union
# (bend/catalog_union.bend) on an events file and prints the catalog it
# makes, line for line as the Rust bridge test prints
# crates/eukhe-models/src/effective.rs `effective_catalog`
# (crates/eukhe-models/src/effective/bridge.rs). Build it with
#
#   bend bend/bridge_catalog_union.bend -o <out>
#
# and run `<out> <events>`. An events file has one entry per line, in the
# order the sources were read (the source of the first line is read
# first):
#
#   b K A D O  a bundled entry: key K, api A, data D, and the optional
#              field O (0 none, N > 0 the value N)
#   c K A D O  a compiled entry, in the same form
#
# Then it prints each entry of the union, in order:
#
#   m K A D O

import Base
import ./catalog_union.bend as CU

# Reading
# -------

def tok.nat(s: String) -> Nat:
  Maybe.default(&2, Nat, Nat.read(s), 0n)

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

def arg(+ws: List<&2, String>, k: Nat) -> Nat:
  tok.nat(tok.at(ws, k))

def opt(n: Nat) -> Maybe<&2, Nat>:
  match n:
    case 0n:
      None{}
    case 1n+m:
      Some{1n+m}

# the scenario's optional field O stands in each of the four (each field
# follows the rule on its own; the Rust side sets one per scenario)
def ent(+ws: List<&2, String>) -> CU.Ent:
  +o = opt(arg(ws, 4n))
  CU.Ent{arg(ws, 1n), arg(ws, 2n), arg(ws, 3n), o, o, o, o}

# the sources read so far: the first source (none before the first
# line), then each source's entries, newest first
type St is Data:
  St{first: List<&2, CU.Src>, bs: List<&2, CU.Ent>, cs: List<&2, CU.Ent>}

# the first source: the one already read, else src
def first.of(fs: List<&2, CU.Src>, +src: CU.Src) -> List<&2, CU.Src>:
  match fs:
    case Nil{}:
      [src]
    case f <> rest:
      f <> rest

def line(h: String, +ws: List<&2, String>, +s: St) -> St:
  match h:
    case SCon{'b', r}:
      match s:
        case St{fs, bs, cs}:
          St{first.of(fs, CU.Bundled{}), ent(ws) <> bs, cs}
    case SCon{'c', r}:
      match s:
        case St{fs, bs, cs}:
          St{first.of(fs, CU.Compiled{}), bs, ent(ws) <> cs}
    case r:
      s

def setup.all(ls: List<&2, String>, +s: St) -> St:
  match ls:
    case Nil{}:
      s
    case l <> rest:
      +ws = String.split(l, ' ')
      setup.all(rest, line(tok.at(ws, 0n), ws, s))

# Writing
# -------

def show.opt(o: Maybe<&2, Nat>) -> String:
  match o:
    case None{}:
      "0"
    case Some{v}:
      Nat.show(v)

def show.ents(xs: List<&2, CU.Ent>) -> String:
  match xs:
    case Nil{}:
      ""
    case CU.Ent{k, a, d, t, c, f, h} <> rest:
      String.concat(["m ", Nat.show(k), " ", Nat.show(a), " ", Nat.show(d), " ", show.opt(t), "\n", show.ents(rest)])

# the catalog of the two sources as the catalog runs it (the fast union;
# the law union_order_free makes the read order free)
def run.go(+bs: List<&2, CU.Ent>, +cs: List<&2, CU.Ent>) -> List<&2, CU.Ent>:
  CU.fast(bs, cs)

def run(s: St) -> String:
  match s:
    case St{fs, bs, cs}:
      show.ents(run.go(List.reverse(&2, CU.Ent, bs), List.reverse(&2, CU.Ent, cs)))

def go(text: String) -> String:
  run(setup.all(String.lines(text), St{Nil{}, Nil{}, Nil{}}))

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
      IO.die(String, 2, "usage: bridge_catalog_union <events>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_catalog_union <events>")
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
