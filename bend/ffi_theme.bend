import Base
import ./wire.bend as W
import ./color.bend as Co
import ./theme/file.bend as TFile
import ./theme/token.bend as TToken
import ./theme/palette.bend as TPalette
import ./theme/bundled.bend as TBundled
import ./theme/choice.bend as TChoice
import ./theme/name.bend as TName
import ./theme/resolve.bend as TResolve

# ffi_theme: the theme rules (bend/theme/: a theme file read and
# completed, the theme a name picks over the files the sources reach, the
# shipped themes' colors) as an entry of the compiled Bend core
# (crates/eukhe-bend/src/rules/theme.rs). Rust reads the files and decodes
# their JSON; this entry decides. Request: a tag, then
#   0  load: a theme file (TPalette.parse)
#   1  resolve: the name, then a count and per file the sources reach:
#      T|F from the custom directory, its stem (Maybe String), its theme
#      file (Maybe file: None when it could not be read or is no theme
#      object) (TResolve.resolve)
#   2  shipped: 0 eukhe, 1 dark, 2 light (TBundled.table)
# A theme file: its name, a count and per variable its name and value, a
# count and per color its key, its token (Maybe U32) and value, then the
# export page, card and info backgrounds (each a Maybe value). A value:
# 0 a string, then the index of the variable it names (Maybe Nat); 1 a
# number as JSON writes it; 2 any other JSON value as written.
# Reply: load: the parse (0 rejected, then why; 1 painted: a count and per
# token its value (0 the terminal default, 1 an index U32, 2 a color), a
# count and per token the color it paints, T|F light, then the file's own
# #rrggbb background, the export page, card and info backgrounds, each a
# Maybe color). Resolve: the theme picked (a U32: 0-2 the builtins, 3 + i
# the file at index i), T|F it warns, the cause (Maybe: 0 the file at
# index i, 1 not found), a count and per clash that warns the file and
# the earlier file it loses to, a count and the other files that did not
# load, a count and per file how it read (0 loaded, 1 invalid, then why,
# 2 no theme object), then the picked file's parse (Maybe). Shipped: a
# count and per token the color it paints. A color: its r g b channels.
# Why a file is invalid: 0 an unknown color key, 1 a color's key and why
# its value is no color, 2 the required tokens it does not write (a count,
# then each U32), 3 an export background (0 page, 1 card, 2 info) and why
# its value is no color; why a value is no color: 0 a circular variable,
# 1 a variable not found, 2 a malformed hex color, 3 any other value, each
# with its text. Any other input (an unknown tag, a short list, a number
# past the wire, input left over): the error form.

type Req is Data:
  Load{f: TFile.RFile}
  Resolve{name: String, files: List<&2, TResolve.Src>}
  Shipped{s: TBundled.Shipped}

# Decoding
# --------

def get_mnat.some(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{n, s}:
      W.Got{Some{n}, s}
    case W.Bad{}:
      W.Bad{}

def get_mnat.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mnat.some(W.get_nat(s))
    case 2n+p:
      W.Bad{}

def get_mnat(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, Nat>>:
  match r:
    case W.Got{t, s}:
      get_mnat.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_jstr.at(x: String, r: W.Dec<Maybe<&2, Nat>>) -> W.Dec<TFile.Json>:
  match r:
    case W.Got{m, s}:
      W.Got{TFile.JStr{x, m}, s}
    case W.Bad{}:
      W.Bad{}

def get_jstr(r: W.Dec<String>) -> W.Dec<TFile.Json>:
  match r:
    case W.Got{x, s}:
      get_jstr.at(x, get_mnat(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_jnum(r: W.Dec<String>) -> W.Dec<TFile.Json>:
  match r:
    case W.Got{x, s}:
      W.Got{TFile.JNum{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_jother(r: W.Dec<String>) -> W.Dec<TFile.Json>:
  match r:
    case W.Got{x, s}:
      W.Got{TFile.JOther{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_json.tag(t: Nat, s: String) -> W.Dec<TFile.Json>:
  match t:
    case 0n:
      get_jstr(W.get_str(s))
    case 1n:
      get_jnum(W.get_str(s))
    case 2n:
      get_jother(W.get_str(s))
    case 3n+p:
      W.Bad{}

# a JSON value
def get_json.go(r: W.Dec<Nat>) -> W.Dec<TFile.Json>:
  match r:
    case W.Got{t, s}:
      get_json.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_var.val(n: String, r: W.Dec<TFile.Json>) -> W.Dec<TFile.Var>:
  match r:
    case W.Got{j, s}:
      W.Got{TFile.Var{n, j}, s}
    case W.Bad{}:
      W.Bad{}

def get_var.go(r: W.Dec<String>) -> W.Dec<TFile.Var>:
  match r:
    case W.Got{n, s}:
      get_var.val(n, get_json.go(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# a variable: its name and value
def get_var(s: String) -> W.Dec<TFile.Var>:
  get_var.go(W.get_str(s))

def get_vars.cons(v: TFile.Var, r: W.Dec<List<&2, TFile.Var>>) -> W.Dec<List<&2, TFile.Var>>:
  match r:
    case W.Got{vs, s}:
      W.Got{v <> vs, s}
    case W.Bad{}:
      W.Bad{}

# the first variable cur, then n more
def get_vars.go(n: Nat, cur: W.Dec<TFile.Var>) -> W.Dec<List<&2, TFile.Var>>:
  match n:
    case 0n:
      match cur:
        case W.Got{v, s}:
          W.Got{[v], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{v, s}:
          get_vars.cons(v, get_vars.go(m, get_var(s)))
        case W.Bad{}:
          W.Bad{}

def get_vars(r: W.Dec<Nat>) -> W.Dec<List<&2, TFile.Var>>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{Nil{}, s}
        case 1n+m:
          get_vars.go(m, get_var(s))
    case W.Bad{}:
      W.Bad{}

def get_mu32.some(r: W.Dec<U32>) -> W.Dec<Maybe<&2, U32>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_mu32.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, U32>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mu32.some(W.get_u32(s))
    case 2n+p:
      W.Bad{}

def get_mu32(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, U32>>:
  match r:
    case W.Got{t, s}:
      get_mu32.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_col.val(k: String, t: Maybe<&2, U32>, r: W.Dec<TFile.Json>) -> W.Dec<TFile.REnt>:
  match r:
    case W.Got{j, s}:
      W.Got{TFile.REnt{k, t, j}, s}
    case W.Bad{}:
      W.Bad{}

def get_col.tok(k: String, r: W.Dec<Maybe<&2, U32>>) -> W.Dec<TFile.REnt>:
  match r:
    case W.Got{t, s}:
      get_col.val(k, t, get_json.go(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_col.go(r: W.Dec<String>) -> W.Dec<TFile.REnt>:
  match r:
    case W.Got{k, s}:
      get_col.tok(k, get_mu32(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# a color entry: its key, its token and its value
def get_col(s: String) -> W.Dec<TFile.REnt>:
  get_col.go(W.get_str(s))

def get_cols.cons(e: TFile.REnt, r: W.Dec<List<&2, TFile.REnt>>) -> W.Dec<List<&2, TFile.REnt>>:
  match r:
    case W.Got{es, s}:
      W.Got{e <> es, s}
    case W.Bad{}:
      W.Bad{}

def get_cols.go(n: Nat, cur: W.Dec<TFile.REnt>) -> W.Dec<List<&2, TFile.REnt>>:
  match n:
    case 0n:
      match cur:
        case W.Got{e, s}:
          W.Got{[e], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{e, s}:
          get_cols.cons(e, get_cols.go(m, get_col(s)))
        case W.Bad{}:
          W.Bad{}

def get_cols(r: W.Dec<Nat>) -> W.Dec<List<&2, TFile.REnt>>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{Nil{}, s}
        case 1n+m:
          get_cols.go(m, get_col(s))
    case W.Bad{}:
      W.Bad{}

def get_mjson.some(r: W.Dec<TFile.Json>) -> W.Dec<Maybe<&2, TFile.Json>>:
  match r:
    case W.Got{j, s}:
      W.Got{Some{j}, s}
    case W.Bad{}:
      W.Bad{}

def get_mjson.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, TFile.Json>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mjson.some(get_json.go(W.get_nat(s)))
    case 2n+p:
      W.Bad{}

def get_mjson(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, TFile.Json>>:
  match r:
    case W.Got{t, s}:
      get_mjson.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_file.info(nm: String, vs: List<&2, TFile.Var>, es: List<&2, TFile.REnt>, pg: Maybe<&2, TFile.Json>, cd: Maybe<&2, TFile.Json>, r: W.Dec<Maybe<&2, TFile.Json>>) -> W.Dec<TFile.RFile>:
  match r:
    case W.Got{io, s}:
      W.Got{TFile.RFile{nm, vs, es, pg, cd, io}, s}
    case W.Bad{}:
      W.Bad{}

def get_file.card(nm: String, vs: List<&2, TFile.Var>, es: List<&2, TFile.REnt>, pg: Maybe<&2, TFile.Json>, r: W.Dec<Maybe<&2, TFile.Json>>) -> W.Dec<TFile.RFile>:
  match r:
    case W.Got{cd, s}:
      get_file.info(nm, vs, es, pg, cd, get_mjson(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_file.page(nm: String, vs: List<&2, TFile.Var>, es: List<&2, TFile.REnt>, r: W.Dec<Maybe<&2, TFile.Json>>) -> W.Dec<TFile.RFile>:
  match r:
    case W.Got{pg, s}:
      get_file.card(nm, vs, es, pg, get_mjson(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_file.cols(nm: String, vs: List<&2, TFile.Var>, r: W.Dec<List<&2, TFile.REnt>>) -> W.Dec<TFile.RFile>:
  match r:
    case W.Got{es, s}:
      get_file.page(nm, vs, es, get_mjson(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_file.vars(nm: String, r: W.Dec<List<&2, TFile.Var>>) -> W.Dec<TFile.RFile>:
  match r:
    case W.Got{vs, s}:
      get_file.cols(nm, vs, get_cols(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# a theme file: its name, variables, colors and export backgrounds
def get_file(r: W.Dec<String>) -> W.Dec<TFile.RFile>:
  match r:
    case W.Got{nm, s}:
      get_file.vars(nm, get_vars(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_mstr.some(r: W.Dec<String>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{x, s}:
      W.Got{Some{x}, s}
    case W.Bad{}:
      W.Bad{}

def get_mstr.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, String>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mstr.some(W.get_str(s))
    case 2n+p:
      W.Bad{}

def get_mstr(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, String>>:
  match r:
    case W.Got{t, s}:
      get_mstr.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_mfile.some(r: W.Dec<TFile.RFile>) -> W.Dec<Maybe<&2, TFile.RFile>>:
  match r:
    case W.Got{f, s}:
      W.Got{Some{f}, s}
    case W.Bad{}:
      W.Bad{}

def get_mfile.tag(t: Nat, s: String) -> W.Dec<Maybe<&2, TFile.RFile>>:
  match t:
    case 0n:
      W.Got{None{}, s}
    case 1n:
      get_mfile.some(get_file(W.get_str(s)))
    case 2n+p:
      W.Bad{}

def get_mfile(r: W.Dec<Nat>) -> W.Dec<Maybe<&2, TFile.RFile>>:
  match r:
    case W.Got{t, s}:
      get_mfile.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_src.body(c: Bool, st: Maybe<&2, String>, r: W.Dec<Maybe<&2, TFile.RFile>>) -> W.Dec<TResolve.Src>:
  match r:
    case W.Got{b, s}:
      W.Got{TResolve.Src{c, st, b}, s}
    case W.Bad{}:
      W.Bad{}

def get_src.stem(c: Bool, r: W.Dec<Maybe<&2, String>>) -> W.Dec<TResolve.Src>:
  match r:
    case W.Got{st, s}:
      get_src.body(c, st, get_mfile(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_src.go(r: W.Dec<Bool>) -> W.Dec<TResolve.Src>:
  match r:
    case W.Got{c, s}:
      get_src.stem(c, get_mstr(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

# a file the sources reach
def get_src(s: String) -> W.Dec<TResolve.Src>:
  get_src.go(W.get_bool(s))

def get_srcs.cons(x: TResolve.Src, r: W.Dec<List<&2, TResolve.Src>>) -> W.Dec<List<&2, TResolve.Src>>:
  match r:
    case W.Got{xs, s}:
      W.Got{x <> xs, s}
    case W.Bad{}:
      W.Bad{}

def get_srcs.go(n: Nat, cur: W.Dec<TResolve.Src>) -> W.Dec<List<&2, TResolve.Src>>:
  match n:
    case 0n:
      match cur:
        case W.Got{x, s}:
          W.Got{[x], s}
        case W.Bad{}:
          W.Bad{}
    case 1n+m:
      match cur:
        case W.Got{x, s}:
          get_srcs.cons(x, get_srcs.go(m, get_src(s)))
        case W.Bad{}:
          W.Bad{}

def get_srcs(r: W.Dec<Nat>) -> W.Dec<List<&2, TResolve.Src>>:
  match r:
    case W.Got{n, s}:
      match n:
        case 0n:
          W.Got{Nil{}, s}
        case 1n+m:
          get_srcs.go(m, get_src(s))
    case W.Bad{}:
      W.Bad{}

def get_load(r: W.Dec<TFile.RFile>) -> W.Dec<Req>:
  match r:
    case W.Got{f, s}:
      W.Got{Load{f}, s}
    case W.Bad{}:
      W.Bad{}

def get_resolve.files(n: String, r: W.Dec<List<&2, TResolve.Src>>) -> W.Dec<Req>:
  match r:
    case W.Got{fs, s}:
      W.Got{Resolve{n, fs}, s}
    case W.Bad{}:
      W.Bad{}

def get_resolve(r: W.Dec<String>) -> W.Dec<Req>:
  match r:
    case W.Got{n, s}:
      get_resolve.files(n, get_srcs(W.get_nat(s)))
    case W.Bad{}:
      W.Bad{}

def get_shipped.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      W.Got{Shipped{TBundled.Eukhe{}}, s}
    case 1n:
      W.Got{Shipped{TBundled.Dark{}}, s}
    case 2n:
      W.Got{Shipped{TBundled.Light{}}, s}
    case 3n+p:
      W.Bad{}

def get_shipped(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_shipped.tag(t, s)
    case W.Bad{}:
      W.Bad{}

def get_req.tag(t: Nat, s: String) -> W.Dec<Req>:
  match t:
    case 0n:
      get_load(get_file(W.get_str(s)))
    case 1n:
      get_resolve(W.get_str(s))
    case 2n:
      get_shipped(W.get_nat(s))
    case 3n+p:
      W.Bad{}

def get_req.go(r: W.Dec<Nat>) -> W.Dec<Req>:
  match r:
    case W.Got{t, s}:
      get_req.tag(t, s)
    case W.Bad{}:
      W.Bad{}

# Replies
# -------

def put_rgb(c: Co.Rgb, rest: String) -> String:
  match c:
    case Co.Rgb{r, g, b}:
      W.put_u32(r, W.put_u32(g, W.put_u32(b, rest)))

def put_rgbs.items(cs: List<&2, Co.Rgb>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      put_rgb(c, put_rgbs.items(t, rest))

def put_mrgb(m: Maybe<&2, Co.Rgb>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{c}:
      W.put_nat(1n, put_rgb(c, rest))

def put_val(v: TFile.Val, rest: String) -> String:
  match v:
    case TFile.Dflt{}:
      W.put_nat(0n, rest)
    case TFile.Idx{i}:
      W.put_nat(1n, W.put_u32(i, rest))
    case TFile.Hex{c}:
      W.put_nat(2n, put_rgb(c, rest))

def put_vals.items(vs: List<&2, TFile.Val>, rest: String) -> String:
  match vs:
    case Nil{}:
      rest
    case v <> t:
      put_val(v, put_vals.items(t, rest))

def put_why(w: TFile.Why, rest: String) -> String:
  match w:
    case TFile.Circular{n}:
      W.put_nat(0n, W.put_str(n, rest))
    case TFile.NotFound{n}:
      W.put_nat(1n, W.put_str(n, rest))
    case TFile.BadHex{t}:
      W.put_nat(2n, W.put_str(t, rest))
    case TFile.BadValue{t}:
      W.put_nat(3n, W.put_str(t, rest))

def put_surf(a: TFile.Surf, rest: String) -> String:
  match a:
    case TFile.OnPage{}:
      W.put_nat(0n, rest)
    case TFile.OnCard{}:
      W.put_nat(1n, rest)
    case TFile.OnInfo{}:
      W.put_nat(2n, rest)

def put_toks.items(ts: List<&2, U32>, rest: String) -> String:
  match ts:
    case Nil{}:
      rest
    case t <> u:
      W.put_u32(t, put_toks.items(u, rest))

def put_fault(f: TFile.Fault, rest: String) -> String:
  match f:
    case TFile.Unknown{k}:
      W.put_nat(0n, W.put_str(k, rest))
    case TFile.InColor{k, w}:
      W.put_nat(1n, W.put_str(k, put_why(w, rest)))
    case TFile.Missing{+ts}:
      W.put_nat(2n, W.put_nat(List.length(&2, U32, ts), put_toks.items(ts, rest)))
    case TFile.InExport{a, w}:
      W.put_nat(3n, put_surf(a, put_why(w, rest)))

def somes(vs: List<&2, TFile.Val>) -> List<&2, Maybe<&2, TFile.Val>>:
  match vs:
    case Nil{}:
      Nil{}
    case v <> t:
      Some{v} <> somes(t)

# the color each of the tokens ts paints in the palette p
def paints(+p: List<&2, Maybe<&2, TFile.Val>>, ts: List<&2, U32>) -> List<&2, Co.Rgb>:
  match ts:
    case Nil{}:
      Nil{}
    case t <> u:
      TPalette.paint(p, t) <> paints(p, u)

def put_parsed(p: TPalette.Parsed, rest: String) -> String:
  match p:
    case TPalette.Rejected{f}:
      W.put_nat(0n, put_fault(f, rest))
    case TPalette.Painted{+vs, l, d, pg, cd, io}:
      +ps = paints(somes(vs), TToken.toks())
      W.put_nat(1n, W.put_nat(List.length(&2, TFile.Val, vs), put_vals.items(vs, W.put_nat(List.length(&2, Co.Rgb, ps), put_rgbs.items(ps, W.put_bool(l, put_mrgb(d, put_mrgb(pg, put_mrgb(cd, put_mrgb(io, rest))))))))))

def put_mparsed(m: Maybe<&2, TPalette.Parsed>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{p}:
      W.put_nat(1n, put_parsed(p, rest))

def put_mcause(m: Maybe<&2, TChoice.Cause>, rest: String) -> String:
  match m:
    case None{}:
      W.put_nat(0n, rest)
    case Some{c}:
      match c:
        case TChoice.FailedAt{at}:
          W.put_nat(1n, W.put_nat(0n, W.put_nat(at, rest)))
        case TChoice.NoTheme{}:
          W.put_nat(1n, W.put_nat(1n, rest))

def put_clashes.items(cs: List<&2, TChoice.Clash>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      match c:
        case TChoice.Clash{at, w}:
          W.put_nat(at, W.put_nat(w, put_clashes.items(t, rest)))

def put_nats.items(ns: List<&2, Nat>, rest: String) -> String:
  match ns:
    case Nil{}:
      rest
    case n <> t:
      W.put_nat(n, put_nats.items(t, rest))

def put_out(o: TResolve.Out, rest: String) -> String:
  match o:
    case TResolve.OLoaded{}:
      W.put_nat(0n, rest)
    case TResolve.OFaulty{f}:
      W.put_nat(1n, put_fault(f, rest))
    case TResolve.ONone{}:
      W.put_nat(2n, rest)

def put_outs.items(os: List<&2, TResolve.Out>, rest: String) -> String:
  match os:
    case Nil{}:
      rest
    case o <> t:
      put_out(o, put_outs.items(t, rest))

def put_resolved(r: TResolve.Resolved) -> String:
  match r:
    case TResolve.Resolved{res, c, +k, +b, +os, p}:
      match res:
        case TName.Res{id, w}:
          W.put_u32(id, W.put_bool(w, put_mcause(c, W.put_nat(List.length(&2, TChoice.Clash, k), put_clashes.items(k, W.put_nat(List.length(&2, Nat, b), put_nats.items(b, W.put_nat(List.length(&2, TResolve.Out, os), put_outs.items(os, put_mparsed(p, ""))))))))))

def reply(r: Req) -> String:
  match r:
    case Load{f}:
      put_parsed(TPalette.parse(f), "")
    case Resolve{n, fs}:
      put_resolved(TResolve.resolve(n, fs))
    case Shipped{s}:
      +cs = TBundled.table(s)
      W.put_nat(List.length(&2, Co.Rgb, cs), put_rgbs.items(cs, ""))

# Running
# -------

def refuse() -> String:
  W.err("theme: malformed request")

def run.end(whole: Bool, r: Req) -> String:
  match whole:
    case True{}:
      reply(r)
    case False{}:
      refuse()

def run(d: W.Dec<Req>) -> String:
  match d:
    case W.Got{r, s}:
      run.end(W.end(s), r)
    case W.Bad{}:
      refuse()

def ffi(input: String) -> String:
  run(get_req.go(W.get_nat(input)))
