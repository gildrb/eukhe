# theme_read (spec): the reader of a request of the theme entry
# (bend/ffi_theme.bend), as the laws of area theme state it
# (laws/theme.bend, section "The compiled entry"): what a request is, read
# with the wire's decoders only (bend/wire.bend; their laws:
# laws/wire.bend). A spec: the shipped code never calls it.

import Base
import ../bend/wire.bend as Wr
import ../bend/theme/file.bend as TFile
import ../bend/theme/bundled.bend as TBundled
import ../bend/theme/resolve.bend as TResolve
import ../bend/ffi_theme.bend as FTh

# The reader
# ----------
# what a request is, read with the wire's decoders: a stage per field

def read.mnat.some(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{n, s}:
      Wr.Got{Some{n}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.mnat.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, Nat>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      read.mnat.some(Wr.get_nat(s))
    case 2n+p:
      Wr.Bad{}

def read.mnat(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, Nat>>:
  match r:
    case Wr.Got{t, s}:
      read.mnat.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read.jstr.at(x: String, r: Wr.Dec<Maybe<&2, Nat>>) -> Wr.Dec<TFile.Json>:
  match r:
    case Wr.Got{m, s}:
      Wr.Got{TFile.JStr{x, m}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.jstr(r: Wr.Dec<String>) -> Wr.Dec<TFile.Json>:
  match r:
    case Wr.Got{x, s}:
      read.jstr.at(x, read.mnat(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read.jnum(r: Wr.Dec<String>) -> Wr.Dec<TFile.Json>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{TFile.JNum{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.jother(r: Wr.Dec<String>) -> Wr.Dec<TFile.Json>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{TFile.JOther{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.json.tag(t: Nat, s: String) -> Wr.Dec<TFile.Json>:
  match t:
    case 0n:
      read.jstr(Wr.get_str(s))
    case 1n:
      read.jnum(Wr.get_str(s))
    case 2n:
      read.jother(Wr.get_str(s))
    case 3n+p:
      Wr.Bad{}

# a JSON value
def read.json.go(r: Wr.Dec<Nat>) -> Wr.Dec<TFile.Json>:
  match r:
    case Wr.Got{t, s}:
      read.json.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read.var.val(n: String, r: Wr.Dec<TFile.Json>) -> Wr.Dec<TFile.Var>:
  match r:
    case Wr.Got{j, s}:
      Wr.Got{TFile.Var{n, j}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.var.go(r: Wr.Dec<String>) -> Wr.Dec<TFile.Var>:
  match r:
    case Wr.Got{n, s}:
      read.var.val(n, read.json.go(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# a variable: its name and value
def read.var(s: String) -> Wr.Dec<TFile.Var>:
  read.var.go(Wr.get_str(s))

def read.vars.cons(v: TFile.Var, r: Wr.Dec<List<&2, TFile.Var>>) -> Wr.Dec<List<&2, TFile.Var>>:
  match r:
    case Wr.Got{vs, s}:
      Wr.Got{v <> vs, s}
    case Wr.Bad{}:
      Wr.Bad{}

# the first variable cur, then n more
def read.vars.go(n: Nat, cur: Wr.Dec<TFile.Var>) -> Wr.Dec<List<&2, TFile.Var>>:
  match n:
    case 0n:
      match cur:
        case Wr.Got{v, s}:
          Wr.Got{[v], s}
        case Wr.Bad{}:
          Wr.Bad{}
    case 1n+m:
      match cur:
        case Wr.Got{v, s}:
          read.vars.cons(v, read.vars.go(m, read.var(s)))
        case Wr.Bad{}:
          Wr.Bad{}

def read.vars(r: Wr.Dec<Nat>) -> Wr.Dec<List<&2, TFile.Var>>:
  match r:
    case Wr.Got{n, s}:
      match n:
        case 0n:
          Wr.Got{Nil{}, s}
        case 1n+m:
          read.vars.go(m, read.var(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read.mu32.some(r: Wr.Dec<U32>) -> Wr.Dec<Maybe<&2, U32>>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Some{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.mu32.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, U32>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      read.mu32.some(Wr.get_u32(s))
    case 2n+p:
      Wr.Bad{}

def read.mu32(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, U32>>:
  match r:
    case Wr.Got{t, s}:
      read.mu32.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read.col.val(k: String, t: Maybe<&2, U32>, r: Wr.Dec<TFile.Json>) -> Wr.Dec<TFile.REnt>:
  match r:
    case Wr.Got{j, s}:
      Wr.Got{TFile.REnt{k, t, j}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.col.tok(k: String, r: Wr.Dec<Maybe<&2, U32>>) -> Wr.Dec<TFile.REnt>:
  match r:
    case Wr.Got{t, s}:
      read.col.val(k, t, read.json.go(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read.col.go(r: Wr.Dec<String>) -> Wr.Dec<TFile.REnt>:
  match r:
    case Wr.Got{k, s}:
      read.col.tok(k, read.mu32(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# a color entry: its key, its token and its value
def read.col(s: String) -> Wr.Dec<TFile.REnt>:
  read.col.go(Wr.get_str(s))

def read.cols.cons(e: TFile.REnt, r: Wr.Dec<List<&2, TFile.REnt>>) -> Wr.Dec<List<&2, TFile.REnt>>:
  match r:
    case Wr.Got{es, s}:
      Wr.Got{e <> es, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.cols.go(n: Nat, cur: Wr.Dec<TFile.REnt>) -> Wr.Dec<List<&2, TFile.REnt>>:
  match n:
    case 0n:
      match cur:
        case Wr.Got{e, s}:
          Wr.Got{[e], s}
        case Wr.Bad{}:
          Wr.Bad{}
    case 1n+m:
      match cur:
        case Wr.Got{e, s}:
          read.cols.cons(e, read.cols.go(m, read.col(s)))
        case Wr.Bad{}:
          Wr.Bad{}

def read.cols(r: Wr.Dec<Nat>) -> Wr.Dec<List<&2, TFile.REnt>>:
  match r:
    case Wr.Got{n, s}:
      match n:
        case 0n:
          Wr.Got{Nil{}, s}
        case 1n+m:
          read.cols.go(m, read.col(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read.mjson.some(r: Wr.Dec<TFile.Json>) -> Wr.Dec<Maybe<&2, TFile.Json>>:
  match r:
    case Wr.Got{j, s}:
      Wr.Got{Some{j}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.mjson.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, TFile.Json>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      read.mjson.some(read.json.go(Wr.get_nat(s)))
    case 2n+p:
      Wr.Bad{}

def read.mjson(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, TFile.Json>>:
  match r:
    case Wr.Got{t, s}:
      read.mjson.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read.file.info(nm: String, vs: List<&2, TFile.Var>, es: List<&2, TFile.REnt>, pg: Maybe<&2, TFile.Json>, cd: Maybe<&2, TFile.Json>, r: Wr.Dec<Maybe<&2, TFile.Json>>) -> Wr.Dec<TFile.RFile>:
  match r:
    case Wr.Got{io, s}:
      Wr.Got{TFile.RFile{nm, vs, es, pg, cd, io}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.file.card(nm: String, vs: List<&2, TFile.Var>, es: List<&2, TFile.REnt>, pg: Maybe<&2, TFile.Json>, r: Wr.Dec<Maybe<&2, TFile.Json>>) -> Wr.Dec<TFile.RFile>:
  match r:
    case Wr.Got{cd, s}:
      read.file.info(nm, vs, es, pg, cd, read.mjson(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read.file.page(nm: String, vs: List<&2, TFile.Var>, es: List<&2, TFile.REnt>, r: Wr.Dec<Maybe<&2, TFile.Json>>) -> Wr.Dec<TFile.RFile>:
  match r:
    case Wr.Got{pg, s}:
      read.file.card(nm, vs, es, pg, read.mjson(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read.file.cols(nm: String, vs: List<&2, TFile.Var>, r: Wr.Dec<List<&2, TFile.REnt>>) -> Wr.Dec<TFile.RFile>:
  match r:
    case Wr.Got{es, s}:
      read.file.page(nm, vs, es, read.mjson(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read.file.vars(nm: String, r: Wr.Dec<List<&2, TFile.Var>>) -> Wr.Dec<TFile.RFile>:
  match r:
    case Wr.Got{vs, s}:
      read.file.cols(nm, vs, read.cols(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# a theme file: its name, variables, colors and export backgrounds
def read.file(r: Wr.Dec<String>) -> Wr.Dec<TFile.RFile>:
  match r:
    case Wr.Got{nm, s}:
      read.file.vars(nm, read.vars(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read.mstr.some(r: Wr.Dec<String>) -> Wr.Dec<Maybe<&2, String>>:
  match r:
    case Wr.Got{x, s}:
      Wr.Got{Some{x}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.mstr.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, String>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      read.mstr.some(Wr.get_str(s))
    case 2n+p:
      Wr.Bad{}

def read.mstr(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, String>>:
  match r:
    case Wr.Got{t, s}:
      read.mstr.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read.mfile.some(r: Wr.Dec<TFile.RFile>) -> Wr.Dec<Maybe<&2, TFile.RFile>>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{Some{f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.mfile.tag(t: Nat, s: String) -> Wr.Dec<Maybe<&2, TFile.RFile>>:
  match t:
    case 0n:
      Wr.Got{None{}, s}
    case 1n:
      read.mfile.some(read.file(Wr.get_str(s)))
    case 2n+p:
      Wr.Bad{}

def read.mfile(r: Wr.Dec<Nat>) -> Wr.Dec<Maybe<&2, TFile.RFile>>:
  match r:
    case Wr.Got{t, s}:
      read.mfile.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read.src.body(c: Bool, st: Maybe<&2, String>, r: Wr.Dec<Maybe<&2, TFile.RFile>>) -> Wr.Dec<TResolve.Src>:
  match r:
    case Wr.Got{b, s}:
      Wr.Got{TResolve.Src{c, st, b}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.src.stem(c: Bool, r: Wr.Dec<Maybe<&2, String>>) -> Wr.Dec<TResolve.Src>:
  match r:
    case Wr.Got{st, s}:
      read.src.body(c, st, read.mfile(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read.src.go(r: Wr.Dec<Bool>) -> Wr.Dec<TResolve.Src>:
  match r:
    case Wr.Got{c, s}:
      read.src.stem(c, read.mstr(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

# a file the sources reach
def read.src(s: String) -> Wr.Dec<TResolve.Src>:
  read.src.go(Wr.get_bool(s))

def read.srcs.cons(x: TResolve.Src, r: Wr.Dec<List<&2, TResolve.Src>>) -> Wr.Dec<List<&2, TResolve.Src>>:
  match r:
    case Wr.Got{xs, s}:
      Wr.Got{x <> xs, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.srcs.go(n: Nat, cur: Wr.Dec<TResolve.Src>) -> Wr.Dec<List<&2, TResolve.Src>>:
  match n:
    case 0n:
      match cur:
        case Wr.Got{x, s}:
          Wr.Got{[x], s}
        case Wr.Bad{}:
          Wr.Bad{}
    case 1n+m:
      match cur:
        case Wr.Got{x, s}:
          read.srcs.cons(x, read.srcs.go(m, read.src(s)))
        case Wr.Bad{}:
          Wr.Bad{}

def read.srcs(r: Wr.Dec<Nat>) -> Wr.Dec<List<&2, TResolve.Src>>:
  match r:
    case Wr.Got{n, s}:
      match n:
        case 0n:
          Wr.Got{Nil{}, s}
        case 1n+m:
          read.srcs.go(m, read.src(s))
    case Wr.Bad{}:
      Wr.Bad{}

def read.load(r: Wr.Dec<TFile.RFile>) -> Wr.Dec<FTh.Req>:
  match r:
    case Wr.Got{f, s}:
      Wr.Got{FTh.Load{f}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.resolve.files(n: String, r: Wr.Dec<List<&2, TResolve.Src>>) -> Wr.Dec<FTh.Req>:
  match r:
    case Wr.Got{fs, s}:
      Wr.Got{FTh.Resolve{n, fs}, s}
    case Wr.Bad{}:
      Wr.Bad{}

def read.resolve(r: Wr.Dec<String>) -> Wr.Dec<FTh.Req>:
  match r:
    case Wr.Got{n, s}:
      read.resolve.files(n, read.srcs(Wr.get_nat(s)))
    case Wr.Bad{}:
      Wr.Bad{}

def read.shipped.tag(t: Nat, s: String) -> Wr.Dec<FTh.Req>:
  match t:
    case 0n:
      Wr.Got{FTh.Shipped{TBundled.Eukhe{}}, s}
    case 1n:
      Wr.Got{FTh.Shipped{TBundled.Dark{}}, s}
    case 2n:
      Wr.Got{FTh.Shipped{TBundled.Light{}}, s}
    case 3n+p:
      Wr.Bad{}

def read.shipped(r: Wr.Dec<Nat>) -> Wr.Dec<FTh.Req>:
  match r:
    case Wr.Got{t, s}:
      read.shipped.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read.req.tag(t: Nat, s: String) -> Wr.Dec<FTh.Req>:
  match t:
    case 0n:
      read.load(read.file(Wr.get_str(s)))
    case 1n:
      read.resolve(Wr.get_str(s))
    case 2n:
      read.shipped(Wr.get_nat(s))
    case 3n+p:
      Wr.Bad{}

def read.req.go(r: Wr.Dec<Nat>) -> Wr.Dec<FTh.Req>:
  match r:
    case Wr.Got{t, s}:
      read.req.tag(t, s)
    case Wr.Bad{}:
      Wr.Bad{}

def read.req.end(whole: Bool, r: FTh.Req) -> Maybe<&2, FTh.Req>:
  match whole:
    case True{}:
      Some{r}
    case False{}:
      None{}

def read.req.whole(d: Wr.Dec<FTh.Req>) -> Maybe<&2, FTh.Req>:
  match d:
    case Wr.Got{r, s}:
      read.req.end(Wr.end(s), r)
    case Wr.Bad{}:
      None{}

# the request s is, when s is exactly one request
def read(s: String) -> Maybe<&2, FTh.Req>:
  read.req.whole(read.req.go(Wr.get_nat(s)))

# the error form the entry refuses with
def refused() -> String:
  SCon{'E', SCon{' ', "theme: malformed request"}}
