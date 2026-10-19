# bridge_theme: runs the theme model (bend/theme.bend, bend/color.bend) on
# a scenario file and prints what it did, line for line as the Rust bridge
# test prints the Rust code (crates/eukhe-core/src/export_html/theme_bridge.rs).
# Build it with
#
#   bend bend/bridge_theme.bend -o <out>
#
# and run `<out> <scenario>`. Each line of the scenario is one query; the
# first word names it, and each printed line answers one query:
#
#   tables                     three lines `table <name> C0 .. C59`: the
#                              color every token of each shipped theme
#                              paints
#   lin                        `lin V0 .. V255`: the linear channel table
#   color R G B R2 G2 B2       `color L light idx text nontext`: the
#                              luminance, light (1/0) and xterm-256 index
#                              of the first color, and whether the pair
#                              meets 9/2 and 3/1 (1/0)
#   ansi I                     `ansi I C`: the color of xterm-256 index I
#   resolve N K..              `resolve ID W`: the theme name N (`-` is the
#                              empty name) resolved over candidates K, each
#                              `R:name:valid:id` (registered) or
#                              `C:name:valid:id` (custom directory), valid
#                              1/0; ID is the theme it resolves to (0, 1, 2
#                              are the builtins eukhe, dark, light), W 1
#                              when it warns
#   file E..                   `file invalid`, or `file ok light C0 .. C59`:
#                              a theme file read and completed. Its entries
#                              E are `V:name:raw` (a variable), `C:t:raw`
#                              (token t's color) and `P:raw` (the export
#                              page background); a raw value is `d` (""),
#                              `iN` (index N), `hRRGGBB`, `b` (a malformed
#                              color) or `rNAME` (the variable NAME)
#
# A color prints as #rrggbb.

import Base
import ./color.bend as Co
import ./theme.bend as T

# Reading
# -------

def tok.at(ws: List<&2, String>, k: Nat) -> String:
  Maybe.default(&2, String, List.get(&2, String, ws, k), "")

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

def num(s: String) -> U32:
  Maybe.default(&2, U32, U32.read(s), 0)

def hexdig(c: Char) -> U32:
  +x = Char.to_u32(c)
  Co.sel(U32.is_ge(x, 97), (x - 87 : U32), (x - 48 : U32))

def hex2(+s: String, +k: Nat) -> U32:
  +hi = hexdig(Maybe.default(&2, Char, String.get(s, k), '0'))
  +lo = hexdig(Maybe.default(&2, Char, String.get(s, 1n+k), '0'))
  (hi * 16 + lo : U32)

def rgb.read(+s: String) -> Co.Rgb:
  Co.Rgb{hex2(s, 0n), hex2(s, 2n), hex2(s, 4n)}

def raw.pick(d: Bool, i: Bool, h: Bool, r: Bool, +rest: String) -> T.Raw:
  match d:
    case True{}:
      T.Lit{T.Dflt{}}
    case False{}:
      match i:
        case True{}:
          T.Lit{T.Idx{num(rest)}}
        case False{}:
          match h:
            case True{}:
              T.Lit{T.Hex{rgb.read(rest)}}
            case False{}:
              match r:
                case True{}:
                  T.Ref{rest}
                case False{}:
                  T.Bad{}

def raw(+s: String) -> T.Raw:
  +c = tok.head(s)
  raw.pick(Char.is_eq(c, 'd'), Char.is_eq(c, 'i'), Char.is_eq(c, 'h'), Char.is_eq(c, 'r'), tok.tail(s))

# Printing
# --------

def hexc(+n: U32) -> Char:
  Char.from_u32(Co.sel(U32.is_lt(n, 10), (n + 48 : U32), (n + 87 : U32)))

def hex2.show(+v: U32) -> String:
  String.from_list([hexc((v >> 4n : U32)), hexc((v .&. 15 : U32))])

def rgb.show(c: Co.Rgb) -> String:
  match c:
    case Co.Rgb{r, g, b}:
      String.concat(["#", hex2.show(r), hex2.show(g), hex2.show(b)])

def bit(b: Bool) -> String:
  match b:
    case True{}:
      "1"
    case False{}:
      "0"

def rgbs.show(xs: List<&2, Co.Rgb>) -> String:
  match xs:
    case Nil{}:
      ""
    case Con{x, rest}:
      String.concat([" ", rgb.show(x), rgbs.show(rest)])

# Queries
# -------

def q.tables() -> String:
  String.concat(["table eukhe", rgbs.show(T.table.eukhe()), "\ntable dark", rgbs.show(T.table.dark()), "\ntable light", rgbs.show(T.table.light()), "\n"])

def q.lin.go(n: Nat, +c: U32) -> String:
  match n:
    case 0n:
      ""
    case 1n+m:
      String.concat([" ", U32.show(Co.lin(c)), q.lin.go(m, (c + 1 : U32))])

def q.lin() -> String:
  String.concat(["lin", q.lin.go(256n, 0), "\n"])

def q.color(+ws: List<&2, String>) -> String:
  +a = {Co.Rgb{num(tok.at(ws, 1n)), num(tok.at(ws, 2n)), num(tok.at(ws, 3n))} : Co.Rgb}
  +b = {Co.Rgb{num(tok.at(ws, 4n)), num(tok.at(ws, 5n)), num(tok.at(ws, 6n))} : Co.Rgb}
  String.concat(["color ", U32.show(Co.lum(a)), " ", bit(Co.light(a)), " ", U32.show(Co.to256(a)), " ", bit(Co.contrast_ge(a, b, 9, 2)), " ", bit(Co.contrast_ge(a, b, 3, 1)), "\n"])

def q.ansi(+ws: List<&2, String>) -> String:
  +i = num(tok.at(ws, 1n))
  String.concat(["ansi ", U32.show(i), " ", rgb.show(Co.ansi256(i)), "\n"])

def cands.keep(keep: Bool, c: T.Cand, rest: List<&2, T.Cand>) -> List<&2, T.Cand>:
  match keep:
    case True{}:
      c <> rest
    case False{}:
      rest

# the candidates of a resolve query: R (registered) or C (custom) ones
def cands(+want: Char, ws: List<&2, String>) -> List<&2, T.Cand>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, rest}:
      +ps = String.split(w, ':')
      cands.keep(Char.is_eq(tok.head(tok.at(ps, 0n)), want), T.Cand{tok.at(ps, 1n), Char.is_eq(tok.head(tok.at(ps, 2n)), '1'), num(tok.at(ps, 3n))}, cands(want, rest))

def name.of(n: String, dash: Bool) -> String:
  match dash:
    case True{}:
      ""
    case False{}:
      n

def q.resolve.show(r: T.Res) -> String:
  match r:
    case T.Res{id, warned}:
      String.concat(["resolve ", U32.show(id), " ", bit(warned), "\n"])

def q.resolve(+ws: List<&2, String>) -> String:
  +n = tok.at(ws, 1n)
  +rest = List.drop(&2, String, ws, 2n)
  +src = T.sources(cands('R', rest), cands('C', rest))
  q.resolve.show(T.resolve.name(src, name.of(n, String.eq(n, "-"))))

def vars.keep(keep: Bool, v: T.Var, rest: List<&2, T.Var>) -> List<&2, T.Var>:
  match keep:
    case True{}:
      v <> rest
    case False{}:
      rest

def vars(ws: List<&2, String>) -> List<&2, T.Var>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, rest}:
      +ps = String.split(w, ':')
      vars.keep(Char.is_eq(tok.head(tok.at(ps, 0n)), 'V'), T.Var{tok.at(ps, 1n), raw(tok.at(ps, 2n))}, vars(rest))

def cols.keep(keep: Bool, e: T.REnt, rest: List<&2, T.REnt>) -> List<&2, T.REnt>:
  match keep:
    case True{}:
      e <> rest
    case False{}:
      rest

def cols(ws: List<&2, String>) -> List<&2, T.REnt>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, rest}:
      +ps = String.split(w, ':')
      cols.keep(Char.is_eq(tok.head(tok.at(ps, 0n)), 'C'), T.REnt{num(tok.at(ps, 1n)), raw(tok.at(ps, 2n))}, cols(rest))

def page.keep(keep: Bool, r: T.Raw, rest: Maybe<&2, T.Raw>) -> Maybe<&2, T.Raw>:
  match keep:
    case True{}:
      Some{r}
    case False{}:
      rest

def page(ws: List<&2, String>) -> Maybe<&2, T.Raw>:
  match ws:
    case Nil{}:
      None{}
    case Con{w, rest}:
      +ps = String.split(w, ':')
      page.keep(Char.is_eq(tok.head(tok.at(ps, 0n)), 'P'), raw(tok.at(ps, 1n)), page(rest))

def paints(+p: List<&2, Maybe<&2, T.Val>>, ts: List<&2, U32>) -> List<&2, Co.Rgb>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      T.paint(p, t) <> paints(p, rest)

def q.file.show(m: Maybe<&2, T.Th>) -> String:
  match m:
    case None{}:
      "file invalid\n"
    case Some{+f}:
      String.concat(["file ok ", bit(T.light(f)), rgbs.show(paints(T.palette(f), T.toks())), "\n"])

def q.file(+ws: List<&2, String>) -> String:
  +rest = List.drop(&2, String, ws, 1n)
  q.file.show(T.load(T.RFile{"f", vars(rest), cols(rest), page(rest)}))

# Running
# -------

def query.pick(tables: Bool, lin: Bool, color: Bool, ansi: Bool, resolve: Bool, file: Bool, +ws: List<&2, String>) -> String:
  match tables:
    case True{}:
      q.tables()
    case False{}:
      match lin:
        case True{}:
          q.lin()
        case False{}:
          match color:
            case True{}:
              q.color(ws)
            case False{}:
              match ansi:
                case True{}:
                  q.ansi(ws)
                case False{}:
                  match resolve:
                    case True{}:
                      q.resolve(ws)
                    case False{}:
                      match file:
                        case True{}:
                          q.file(ws)
                        case False{}:
                          ""

def query(+w: String, +ws: List<&2, String>) -> String:
  query.pick(String.eq(w, "tables"), String.eq(w, "lin"), String.eq(w, "color"), String.eq(w, "ansi"), String.eq(w, "resolve"), String.eq(w, "file"), ws)

def run(ls: List<&2, String>) -> String:
  match ls:
    case Nil{}:
      ""
    case l <> rest:
      +ws = String.split(l, ' ')
      String.append(query(tok.at(ws, 0n), ws), run(rest))

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
      IO.die(String, 2, "usage: bridge_theme <scenario>")
    case prog <> rest:
      match rest:
        case Nil{}:
          IO.die(String, 2, "usage: bridge_theme <scenario>")
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
