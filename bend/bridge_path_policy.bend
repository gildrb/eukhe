# bridge_path_policy: runs the path policy model (bend/path_policy.bend,
# LAWS.bend section path_policy) on a scenario file and prints what it did, line
# for line as the Rust bridge test prints the path policy and the
# document tools' gate (crates/eukhe-core/src/durable/path_policy/
# bridge.rs). Build it with
#
#   bend bend/bridge_path_policy.bend -o <out>
#
# and run `<out> <scenario>`. A token is one of:
#
#   nK      the name K (a segment Name{K} in a path)
#   u       Up (`..`)
#   h       Here (`.`)
#   aDDD    an auto set: each digit D is an effect code (read 0, write 1,
#           exec 2, net 3, outside 4, protected 5, secret 6)
#   y n g   an answer: Yes, No, Gone (no one answered)
#
# A path is its segments from `/`; a location is its names from `/`.
# Each line of a scenario is one event:
#
#   k B NAMES ; SEGS        a symlink at NAMES; B 1: its target SEGS is
#                           from `/`, B 0: from the link's directory
#   r SEGS                  a workspace root
#   t SEGS                  a protected Tree rule
#   d SEGS                  a protected Dir rule
#   m nK                    a protected Named rule of name K
#   s SEGS                  a secret entry
#   c V NAMES               a file at NAMES that holds V
#   q A X A X A X A X SEGS  a query of SEGS: for the accesses Rd, Ls,
#                           Sr, Wr in this order, the auto set and the
#                           answer of the user
#   x A                     the auto set of the writes
#   w X V SEGS              an agent's write of V through SEGS; X is the
#                           answer of the user if the gate asks
#
# The policy's entries are the real paths of their SEGS (as
# eukhe_types::path_policy::PathPolicy::new makes them). The output has,
# in order:
#
#   q L C H RA RA RA RA NAMES   for each query: L 1 when its links
#                               looped, its class C (i, o, p, s), H 1 when
#                               it holds a secret, then for each access R
#                               1 when it runs and A 1 when the gate
#                               asked, and the names of its real path
#   w 1 NAMES / w 0             for each write: whether the gate asked,
#                               and the real path it asked about
#   g V NAMES                   for each guarded (protected or secret)
#                               file after the writes: its value and its
#                               location (Pp.guarded of Pp.run)
#
# Each name in the output is ` nK`, from `/`.

import Base
import ./tools.bend as Tl
import ./path_policy.bend as Pp

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

def tok.tail(s: String) -> String:
  match s:
    case SNil{}:
      ""
    case SCon{c, t}:
      t

# the line's tokens are of kind c
def kind(ts: List<&2, String>, c: Char) -> Bool:
  Char.is_eq(tok.head(tok.at(ts, 0n)), c)

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

# a token: `nN`, `u` or `h`
def seg.of(name: Bool, up: Bool, n: Nat) -> Tl.Seg:
  match name:
    case True{}:
      Tl.Name{n}
    case False{}:
      match up:
        case True{}:
          Tl.Up{}
        case False{}:
          Tl.Here{}

def seg(+w: String) -> Tl.Seg:
  +c = tok.head(w)
  seg.of(Char.is_eq(c, 'n'), Char.is_eq(c, 'u'), tok.nat(tok.tail(w)))

def segs(ws: List<&2, String>) -> List<&2, Tl.Seg>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      match w:
        case SNil{}:
          segs(rest)
        case SCon{c, t}:
          seg(SCon{c, t}) <> segs(rest)

# the names of `nK` tokens, from `/`
def names(ws: List<&2, String>) -> List<&2, Nat>:
  match ws:
    case Nil{}:
      Nil{}
    case w <> rest:
      match w:
        case SNil{}:
          names(rest)
        case SCon{c, t}:
          tok.nat(t) <> names(rest)

# the location of `nK` tokens (deepest first)
def deep(ws: List<&2, String>) -> List<&2, Nat>:
  List.reverse(&2, Nat, names(ws))

def upto.pick(stop: Bool, w: String, rest: List<&2, String>) -> List<&2, String>:
  match stop:
    case True{}:
      Nil{}
    case False{}:
      w <> rest

# the tokens before `;`
def upto(ws: List<&2, String>) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case +w <> rest:
      upto.pick(Char.is_eq(tok.head(w), ';'), w, upto(rest))

# the tokens after `;`
def past(ws: List<&2, String>) -> List<&2, String>:
  match ws:
    case Nil{}:
      Nil{}
    case +w <> +rest:
      Bool.pick(List<&2, String>, Char.is_eq(tok.head(w), ';'), rest, past(rest))

def auto.of(s: String) -> List<&2, Nat>:
  match s:
    case SNil{}:
      Nil{}
    case SCon{c, t}:
      U32.to_nat((Char.to_u32(c) - 48 : U32)) <> auto.of(t)

# an `aDDD` token
def auto(w: String) -> List<&2, Nat>:
  auto.of(tok.tail(w))

def ans.of(y: Bool, n: Bool) -> Pp.Ans:
  match y:
    case True{}:
      Pp.Yes{}
    case False{}:
      match n:
        case True{}:
          Pp.No{}
        case False{}:
          Pp.Gone{}

def ans(+w: String) -> Pp.Ans:
  ans.of(Char.is_eq(tok.head(w), 'y'), Char.is_eq(tok.head(w), 'n'))

# The scenario
# ------------

def links(ls: List<&2, String>) -> List<&2, Pp.Link>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      +ts = String.split(l, ' ')
      +body = List.drop(&2, String, ts, 2n)
      List.filter.put(Pp.Link, Pp.Link{deep(upto(body)), Char.is_eq(tok.head(tok.at(ts, 1n)), '1'), segs(past(body))}, links(rest), kind(ts, 'k'))

# the real paths of the lines of kind c
def reals(ls: List<&2, String>, +c: Char, +links: List<&2, Pp.Link>) -> List<&2, List<&2, Nat>>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      +ts = String.split(l, ' ')
      List.filter.put(List<&2, Nat>, Pp.Res.at(Pp.real(links, segs(List.drop(&2, String, ts, 1n)))), reals(rest, c, links), kind(ts, c))

def rule.pick(t: Bool, d: Bool, m: Bool, p: List<&2, Nat>, n: Nat, rest: List<&2, Pp.Rule>) -> List<&2, Pp.Rule>:
  match t:
    case True{}:
      Pp.Tree{p} <> rest
    case False{}:
      match d:
        case True{}:
          Pp.Dir{p} <> rest
        case False{}:
          match m:
            case True{}:
              Pp.Named{n} <> rest
            case False{}:
              rest

def rules(ls: List<&2, String>, +links: List<&2, Pp.Link>) -> List<&2, Pp.Rule>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      +ts = String.split(l, ' ')
      rule.pick(kind(ts, 't'), kind(ts, 'd'), kind(ts, 'm'), Pp.Res.at(Pp.real(links, segs(List.drop(&2, String, ts, 1n)))), tok.nat(tok.tail(tok.at(ts, 1n))), rules(rest, links))

def cells(ls: List<&2, String>) -> List<&2, Pp.Cell>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      +ts = String.split(l, ' ')
      List.filter.put(Pp.Cell, Pp.Cell{deep(List.drop(&2, String, ts, 2n)), tok.nat(tok.at(ts, 1n))}, cells(rest), kind(ts, 'c'))

def puts(ls: List<&2, String>) -> List<&2, Pp.Put>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      +ts = String.split(l, ' ')
      List.filter.put(Pp.Put, Pp.Put{segs(List.drop(&2, String, ts, 3n)), tok.nat(tok.at(ts, 2n)), ans(tok.at(ts, 1n))}, puts(rest), kind(ts, 'w'))

# the auto set of the writes (the first `x` line)
def store.auto(ls: List<&2, String>) -> List<&2, Nat>:
  match ls:
    case Nil{}:
      Nil{}
    case l <> rest:
      +ts = String.split(l, ' ')
      Bool.pick(List<&2, Nat>, kind(ts, 'x'), auto(tok.at(ts, 1n)), store.auto(rest))

# Showing
# -------

def names.show(xs: List<&2, Nat>) -> String:
  match xs:
    case Nil{}:
      ""
    case x <> rest:
      String.concat([" n", Nat.show(x), names.show(rest)])

# a location (deepest first), from `/`
def at.show(at: List<&2, Nat>) -> String:
  names.show(List.reverse(&2, Nat, at))

def cls.show(c: Pp.Cls) -> String:
  match c:
    case Pp.Inside{}:
      "i"
    case Pp.Outside{}:
      "o"
    case Pp.Protected{}:
      "p"
    case Pp.Secret{}:
      "s"

# whether access a runs, and whether the gate asked
def check(+c: Pp.Cls, +a: Pp.Acc, +auto: List<&2, Nat>, ans: Pp.Ans) -> String:
  String.append(bit(Pp.runs(c, a, auto, ans)), bit(Pp.asks(c, a, auto)))

def query(+pol: Pp.Pol, +ls: List<&2, Pp.Link>, +ts: List<&2, String>) -> String:
  +ss = segs(List.drop(&2, String, ts, 9n))
  +r = Pp.real(ls, ss)
  +c = Pp.class(pol, ls, ss)
  +h = Pp.holds(pol, ls, ss)
  String.concat(["q ", bit(Pp.Res.looped(r)), " ", cls.show(c), " ", bit(h), " ", check(c, Pp.Rd{}, auto(tok.at(ts, 1n)), ans(tok.at(ts, 2n))), " ", check(c, Pp.Ls{}, auto(tok.at(ts, 3n)), ans(tok.at(ts, 4n))), " ", check(c, Pp.Sr{h}, auto(tok.at(ts, 5n)), ans(tok.at(ts, 6n))), " ", check(c, Pp.Wr{}, auto(tok.at(ts, 7n)), ans(tok.at(ts, 8n))), at.show(Pp.Res.at(r)), "\n"])

def write.line(asked: Bool, at: List<&2, Nat>) -> String:
  match asked:
    case True{}:
      String.concat(["w 1", at.show(at), "\n"])
    case False{}:
      "w 0\n"

def write(+pol: Pp.Pol, +ls: List<&2, Pp.Link>, +auto: List<&2, Nat>, +ts: List<&2, String>) -> String:
  +ss = segs(List.drop(&2, String, ts, 3n))
  write.line(Pp.asks(Pp.class(pol, ls, ss), Pp.Wr{}, auto), Pp.Res.at(Pp.real(ls, ss)))

def out.pick(q: Bool, w: Bool, +pol: Pp.Pol, +ls: List<&2, Pp.Link>, +auto: List<&2, Nat>, +ts: List<&2, String>) -> String:
  match q:
    case True{}:
      query(pol, ls, ts)
    case False{}:
      match w:
        case True{}:
          write(pol, ls, auto, ts)
        case False{}:
          ""

def outs(lines: List<&2, String>, +pol: Pp.Pol, +ls: List<&2, Pp.Link>, +auto: List<&2, Nat>) -> String:
  match lines:
    case Nil{}:
      ""
    case l <> rest:
      +ts = String.split(l, ' ')
      String.append(out.pick(kind(ts, 'q'), kind(ts, 'w'), pol, ls, auto, ts), outs(rest, pol, ls, auto))

def cells.show(cs: List<&2, Pp.Cell>) -> String:
  match cs:
    case Nil{}:
      ""
    case c <> rest:
      match c:
        case Pp.Cell{at, v}:
          String.concat(["g ", Nat.show(v), at.show(at), "\n", cells.show(rest)])

def run(+lines: List<&2, String>) -> String:
  +ls = links(lines)
  +pol = {Pp.Pol{reals(lines, 'r', ls), rules(lines, ls), reals(lines, 's', ls)} : Pp.Pol}
  +auto = store.auto(lines)
  String.append(outs(lines, pol, ls, auto), cells.show(Pp.guarded(Pp.run(puts(lines), pol, ls, auto, cells(lines)), pol)))

# Running
# -------

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
      IO.die(String, 2, "usage: bridge_path_policy <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_path_policy <scenario>")
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
