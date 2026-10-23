# bridge_theme: runs the theme model (bend/theme/, bend/color.bend) on
# a scenario file and prints what it did, line for line as the Rust bridge
# test prints the Rust code (crates/eukhe-core/src/export_html/theme_bridge.rs).
# Build it with
#
#   bend bridge/bridge_theme.bend -o <out>
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
#   resolve N K..              `resolve ID W CAUSE CLASHES BROKEN`: the
#                              theme name N (`-` is the empty name) picked
#                              over the files K, each `R:name:valid:id`
#                              (registered) or `C:name:valid:id` (custom
#                              directory), valid 1/0; ID is the theme it
#                              picks (0, 1, 2 are the builtins eukhe, dark,
#                              light, else a file's id), W 1 when it warns,
#                              CAUSE `-` (no warning), `n` (not found) or the
#                              id of the failed file it blames, CLASHES
#                              `,id>winner` per clash, BROKEN `,id` per other
#                              failed file
#   file E..                   `file invalid REASON` (the reason the user
#                              sees), or `file ok light C0 .. C58 D P K I`:
#                              a theme file read and completed, with its
#                              own #rrggbb background and its export page,
#                              card and info backgrounds (`-`: none). Its
#                              entries E are `V:name:raw` (a variable, in
#                              name order), `C:key:raw` (a color, in key
#                              order), `P:raw`, `K:raw` and `I:raw` (the
#                              export page, card and info backgrounds); a
#                              raw value is `d` (""), `hTEXT` (#TEXT),
#                              `rNAME` (the string NAME), `nTEXT` (a number
#                              JSON writes as TEXT) or `oTEXT` (any other
#                              JSON value, as written)
#
# A color prints as #rrggbb.

import Base
import ../bend/color.bend as Co
import ../bend/theme/file.bend as TFile
import ../bend/theme/token.bend as TToken
import ../bend/theme/palette.bend as TPalette
import ../bend/theme/bundled.bend as TBundled
import ../bend/theme/name.bend as TName
import ../bend/theme/choice.bend as TChoice

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

# the token names, in token order
def names() -> List<&2, String>:
  ["accent", "border", "borderAccent", "borderMuted", "success", "error", "warning", "muted", "dim", "text", "thinkingText", "userMessageText", "customMessageText", "customMessageLabel", "refinementHeader", "refinementSummary", "toolTitle", "toolOutput", "mdBody", "mdHeading", "mdLink", "mdLinkUrl", "mdCode", "mdCodeBlock", "mdCodeBlockBorder", "mdQuote", "mdQuoteBorder", "mdHr", "mdListBullet", "toolDiffAdded", "toolDiffRemoved", "toolDiffText", "toolDiffContext", "syntaxComment", "syntaxKeyword", "syntaxFunction", "syntaxVariable", "syntaxString", "syntaxNumber", "syntaxType", "syntaxOperator", "syntaxPunctuation", "effortLow", "effortHigh", "contextHigh", "liftLight", "liftDark", "bashMode", "selectedBg", "userMessageBg", "customMessageBg", "toolPendingBg", "toolSuccessBg", "toolErrorBg", "toolDiffAddedBg", "toolDiffRemovedBg", "toolPanelBg", "background", "foreground"]

def index.pick(hit: Bool, at: Nat, other: Maybe<&2, Nat>) -> Maybe<&2, Nat>:
  match hit:
    case True{}:
      Some{at}
    case False{}:
      other

# the index of the first n in xs
def index(xs: List<&2, String>, +n: String, +at: Nat) -> Maybe<&2, Nat>:
  match xs:
    case Nil{}:
      None{}
    case Con{x, rest}:
      index.pick(String.eq(x, n), at, index(rest, n, 1n+at))

def tok.u32(m: Maybe<&2, Nat>) -> Maybe<&2, U32>:
  match m:
    case None{}:
      None{}
    case Some{n}:
      Some{U32.from_nat(n)}

# the token a color key names
def tok.of(+key: String) -> Maybe<&2, U32>:
  tok.u32(index(names(), key, 0n))

def json.pick(d: Bool, h: Bool, r: Bool, n: Bool, +rest: String, +vn: List<&2, String>) -> TFile.Json:
  match d:
    case True{}:
      TFile.JStr{"", None{}}
    case False{}:
      match h:
        case True{}:
          TFile.JStr{SCon{'#', rest}, None{}}
        case False{}:
          match r:
            case True{}:
              TFile.JStr{rest, index(vn, rest, 0n)}
            case False{}:
              match n:
                case True{}:
                  TFile.JNum{rest}
                case False{}:
                  TFile.JOther{rest}

# a raw value word: d (""), hTEXT (#TEXT), rNAME (the string NAME), nTEXT
# (the number JSON writes as TEXT), oTEXT (any other JSON value, as
# written); a string carries the index of the variable it names
def json(+s: String, +vn: List<&2, String>) -> TFile.Json:
  +c = tok.head(s)
  json.pick(Char.is_eq(c, 'd'), Char.is_eq(c, 'h'), Char.is_eq(c, 'r'), Char.is_eq(c, 'n'), tok.tail(s), vn)
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
  String.concat(["table eukhe", rgbs.show(TPalette.table.eukhe()), "\ntable dark", rgbs.show(TBundled.table.dark()), "\ntable light", rgbs.show(TPalette.table.light()), "\n"])

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

def words.keep(keep: Bool, p: List<&2, String>, rest: List<&2, List<&2, String>>) -> List<&2, List<&2, String>>:
  match keep:
    case True{}:
      p <> rest
    case False{}:
      rest

# the words of a query that start with c, split at ':'
def word.has(ws: List<&2, String>, +c: Char) -> List<&2, List<&2, String>>:
  match ws:
    case Nil{}:
      Nil{}
    case Con{w, rest}:
      +ps = String.split(w, ':')
      words.keep(Char.is_eq(tok.head(tok.at(ps, 0n)), c), ps, word.has(rest, c))

def ld.of(valid: Bool, nm: String, +custom: Bool) -> TChoice.Ld:
  match valid:
    case True{}:
      TChoice.Fine{nm, custom}
    case False{}:
      TChoice.Broke{Some{nm}, None{}}

# the files of a resolve query: `R:name:valid:id` (registered) or
# `C:name:valid:id` (custom directory), valid 1/0
def lds(ps: List<&2, List<&2, String>>, +custom: Bool) -> List<&2, TChoice.Ld>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      ld.of(Char.is_eq(tok.head(tok.at(p, 2n)), '1'), tok.at(p, 1n), custom) <> lds(rest, custom)

def ids(ps: List<&2, List<&2, String>>) -> List<&2, U32>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      num(tok.at(p, 3n)) <> ids(rest)

def name.of(n: String, dash: Bool) -> String:
  match dash:
    case True{}:
      ""
    case False{}:
      n

def id.at(+fs: List<&2, U32>, at: Nat) -> String:
  U32.show(Maybe.default(&2, U32, List.get(&2, U32, fs, at), 999))

def id.show(low: Bool, +id: U32, +fs: List<&2, U32>) -> String:
  match low:
    case True{}:
      U32.show(id)
    case False{}:
      id.at(fs, U32.to_nat((id - 3 : U32)))

def cause.show(m: Maybe<&2, TChoice.Cause>, +fs: List<&2, U32>) -> String:
  match m:
    case None{}:
      "-"
    case Some{c}:
      match c:
        case TChoice.NoTheme{}:
          "n"
        case TChoice.FailedAt{at}:
          id.at(fs, at)

def clashes.show(cs: List<&2, TChoice.Clash>, +fs: List<&2, U32>) -> String:
  match cs:
    case Nil{}:
      ""
    case Con{c, rest}:
      match c:
        case TChoice.Clash{at, w}:
          String.concat([",", id.at(fs, at), ">", id.at(fs, w), clashes.show(rest, fs)])

def broken.show(bs: List<&2, Nat>, +fs: List<&2, U32>) -> String:
  match bs:
    case Nil{}:
      ""
    case Con{b, rest}:
      String.concat([",", id.at(fs, b), broken.show(rest, fs)])

def q.resolve.show(p: TChoice.Pick, +fs: List<&2, U32>) -> String:
  match p:
    case TChoice.Pick{r, c, k, b}:
      match r:
        case TName.Res{+id, warned}:
          String.concat(["resolve ", id.show(U32.is_lt(id, 3), id, fs), " ", bit(warned), " ", cause.show(c, fs), " ", clashes.show(k, fs), " ", broken.show(b, fs), "\n"])

def q.resolve(+ws: List<&2, String>) -> String:
  +n = tok.at(ws, 1n)
  +rest = List.drop(&2, String, ws, 2n)
  +rs = word.has(rest, 'R')
  +cs = word.has(rest, 'C')
  +ls = List.append(&2, TChoice.Ld, lds(rs, False{}), lds(cs, True{}))
  q.resolve.show(TChoice.pick(ls, name.of(n, String.eq(n, "-"))), List.append(&2, U32, ids(rs), ids(cs)))

# the variable names of a file query, in order
def var.names(ps: List<&2, List<&2, String>>) -> List<&2, String>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      tok.at(p, 1n) <> var.names(rest)

def vars(ps: List<&2, List<&2, String>>, +vn: List<&2, String>) -> List<&2, TFile.Var>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      TFile.Var{tok.at(p, 1n), json(tok.at(p, 2n), vn)} <> vars(rest, vn)

def cols(ps: List<&2, List<&2, String>>, +vn: List<&2, String>) -> List<&2, TFile.REnt>:
  match ps:
    case Nil{}:
      Nil{}
    case Con{+p, rest}:
      +key = tok.at(p, 1n)
      TFile.REnt{key, tok.of(key), json(tok.at(p, 2n), vn)} <> cols(rest, vn)

def surf(ps: List<&2, List<&2, String>>, +vn: List<&2, String>) -> Maybe<&2, TFile.Json>:
  match ps:
    case Nil{}:
      None{}
    case Con{+p, rest}:
      Some{json(tok.at(p, 1n), vn)}

def paints(+p: List<&2, Maybe<&2, TFile.Val>>, ts: List<&2, U32>) -> List<&2, Co.Rgb>:
  match ts:
    case Nil{}:
      Nil{}
    case Con{t, rest}:
      TPalette.paint(p, t) <> paints(p, rest)

def somes(vs: List<&2, TFile.Val>) -> List<&2, Maybe<&2, TFile.Val>>:
  match vs:
    case Nil{}:
      Nil{}
    case Con{v, rest}:
      Some{v} <> somes(rest)

def opt.show(m: Maybe<&2, Co.Rgb>) -> String:
  match m:
    case None{}:
      "-"
    case Some{c}:
      rgb.show(c)

def why.show(w: TFile.Why) -> String:
  match w:
    case TFile.Circular{n}:
      String.append("Circular variable reference detected: ", n)
    case TFile.NotFound{n}:
      String.append("Variable reference not found: ", n)
    case TFile.BadHex{t}:
      String.append("Invalid hex color: ", t)
    case TFile.BadValue{t}:
      String.append("Invalid color value: ", t)

def surf.key(s: TFile.Surf) -> String:
  match s:
    case TFile.OnPage{}:
      "pageBg"
    case TFile.OnCard{}:
      "cardBg"
    case TFile.OnInfo{}:
      "infoBg"

def name.of.tok(+t: U32) -> String:
  Maybe.default(&2, String, List.get(&2, String, names(), U32.to_nat(t)), "?")

def missing.show(ts: List<&2, U32>, first: Bool) -> String:
  match ts:
    case Nil{}:
      ""
    case Con{t, rest}:
      match first:
        case True{}:
          String.append(name.of.tok(t), missing.show(rest, False{}))
        case False{}:
          String.append(", ", String.append(name.of.tok(t), missing.show(rest, False{})))

def fault.show(f: TFile.Fault) -> String:
  match f:
    case TFile.Unknown{k}:
      String.append("unknown color token: ", k)
    case TFile.InColor{k, w}:
      String.append("color \"", String.append(k, String.append("\": ", why.show(w))))
    case TFile.Missing{ts}:
      String.append("missing required color tokens: ", missing.show(ts, True{}))
    case TFile.InExport{s, w}:
      String.append("export \"", String.append(surf.key(s), String.append("\": ", why.show(w))))

def q.file.show(p: TPalette.Parsed) -> String:
  match p:
    case TPalette.Rejected{f}:
      String.append("file invalid ", String.append(fault.show(f), "\n"))
    case TPalette.Painted{vs, light, d, pg, cd, io}:
      String.concat(["file ok ", bit(light), rgbs.show(paints(somes(vs), TToken.toks())), " ", opt.show(d), " ", opt.show(pg), " ", opt.show(cd), " ", opt.show(io), "\n"])

def q.file(+ws: List<&2, String>) -> String:
  +rest = List.drop(&2, String, ws, 1n)
  +vs = word.has(rest, 'V')
  +vn = var.names(vs)
  q.file.show(TPalette.parse(TFile.RFile{"f", vars(vs, vn), cols(word.has(rest, 'C'), vn), surf(word.has(rest, 'P'), vn), surf(word.has(rest, 'K'), vn), surf(word.has(rest, 'I'), vn)}))

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
