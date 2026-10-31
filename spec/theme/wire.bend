# theme_wire (spec): the wire of the theme entry (bend/ffi_theme.bend) as
# the laws of area theme read it (laws/theme.bend, section "The compiled
# entry"): the requests and replies spelled with the wire primitives only
# (bend/wire.bend; their round trips: laws/wire.bend), what fits the wire,
# the reader of a request, and the spec of one load (what a name resolves
# to over the files the sources reach, with the clashes that warn) and of
# the color each token paints. A spec: the shipped code never calls it.

import Base
import ../../bend/wire.bend as Wr
import ../../bend/color.bend as Co
import ../../bend/theme/file.bend as TFile
import ../../bend/theme/palette.bend as TPalette
import ../../bend/theme/bundled.bend as TBundled
import ../../bend/theme/choice.bend as TChoice
import ../../bend/theme/name.bend as TName
import ../../bend/theme/resolve.bend as TResolve
import ../../bend/ffi_theme.bend as FTh
import ../../laws/base.bend as LawsBase

# Requests, as Rust writes them
# -----------------------------

def mnat(m: Maybe<&2, Nat>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{n}:
      Wr.put_nat(1n, Wr.put_nat(n, rest))

def json(j: TFile.Json, rest: String) -> String:
  match j:
    case TFile.JStr{x, at}:
      Wr.put_nat(0n, Wr.put_str(x, mnat(at, rest)))
    case TFile.JNum{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))
    case TFile.JOther{x}:
      Wr.put_nat(2n, Wr.put_str(x, rest))

def var(v: TFile.Var, rest: String) -> String:
  match v:
    case TFile.Var{n, j}:
      Wr.put_str(n, json(j, rest))

def vars.items(vs: List<&2, TFile.Var>, rest: String) -> String:
  match vs:
    case Nil{}:
      rest
    case v <> t:
      var(v, vars.items(t, rest))

def mu32(m: Maybe<&2, U32>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_u32(x, rest))

def col(e: TFile.REnt, rest: String) -> String:
  match e:
    case TFile.REnt{k, t, j}:
      Wr.put_str(k, mu32(t, json(j, rest)))

def cols.items(es: List<&2, TFile.REnt>, rest: String) -> String:
  match es:
    case Nil{}:
      rest
    case e <> t:
      col(e, cols.items(t, rest))

def mjson(m: Maybe<&2, TFile.Json>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{j}:
      Wr.put_nat(1n, json(j, rest))

# a theme file: its name, a count and its variables, a count and its
# colors, then its export page, card and info backgrounds
def file(f: TFile.RFile, rest: String) -> String:
  match f:
    case TFile.RFile{nm, +vs, +es, pg, cd, io}:
      Wr.put_str(nm, Wr.put_nat(List.length(&2, TFile.Var, vs), vars.items(vs, Wr.put_nat(List.length(&2, TFile.REnt, es), cols.items(es, mjson(pg, mjson(cd, mjson(io, rest))))))))

def mstr(m: Maybe<&2, String>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{x}:
      Wr.put_nat(1n, Wr.put_str(x, rest))

def mfile(m: Maybe<&2, TFile.RFile>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{f}:
      Wr.put_nat(1n, file(f, rest))

def src(s: TResolve.Src, rest: String) -> String:
  match s:
    case TResolve.Src{c, st, b}:
      Wr.put_bool(c, mstr(st, mfile(b, rest)))

def srcs.items(ss: List<&2, TResolve.Src>, rest: String) -> String:
  match ss:
    case Nil{}:
      rest
    case s <> t:
      src(s, srcs.items(t, rest))

def shipped(s: TBundled.Shipped, rest: String) -> String:
  match s:
    case TBundled.Eukhe{}:
      Wr.put_nat(0n, rest)
    case TBundled.Dark{}:
      Wr.put_nat(1n, rest)
    case TBundled.Light{}:
      Wr.put_nat(2n, rest)

# a request, then rest
def req(r: FTh.Req, rest: String) -> String:
  match r:
    case FTh.Load{f}:
      Wr.put_nat(0n, file(f, rest))
    case FTh.Resolve{n, +ss}:
      Wr.put_nat(1n, Wr.put_str(n, Wr.put_nat(List.length(&2, TResolve.Src, ss), srcs.items(ss, rest))))
    case FTh.Shipped{s}:
      Wr.put_nat(2n, shipped(s, rest))

# What fits the wire
# ------------------
# every text's length, every count and every variable index: at most 14
# digits

def fits.str(+x: String) -> Bool:
  LawsBase.wire_fits(String.length(x))

def fits.mnat(m: Maybe<&2, Nat>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{n}:
      LawsBase.wire_fits(n)

def fits.json(j: TFile.Json) -> Bool:
  match j:
    case TFile.JStr{x, at}:
      Bool.and(fits.str(x), fits.mnat(at))
    case TFile.JNum{x}:
      fits.str(x)
    case TFile.JOther{x}:
      fits.str(x)

def fits.mjson(m: Maybe<&2, TFile.Json>) -> Bool:
  match m:
    case None{}:
      True{}
    case Some{j}:
      fits.json(j)

def fits.vars(vs: List<&2, TFile.Var>) -> Bool:
  match vs:
    case Nil{}:
      True{}
    case v <> t:
      match v:
        case TFile.Var{n, j}:
          Bool.and(fits.str(n), Bool.and(fits.json(j), fits.vars(t)))

def fits.cols(es: List<&2, TFile.REnt>) -> Bool:
  match es:
    case Nil{}:
      True{}
    case e <> t:
      match e:
        case TFile.REnt{k, x, j}:
          Bool.and(fits.str(k), Bool.and(fits.json(j), fits.cols(t)))

def fits.file(f: TFile.RFile) -> Bool:
  match f:
    case TFile.RFile{nm, +vs, +es, pg, cd, io}:
      Bool.and(fits.str(nm), Bool.and(LawsBase.wire_fits(List.length(&2, TFile.Var, vs)), Bool.and(fits.vars(vs), Bool.and(LawsBase.wire_fits(List.length(&2, TFile.REnt, es)), Bool.and(fits.cols(es), Bool.and(fits.mjson(pg), Bool.and(fits.mjson(cd), fits.mjson(io))))))))

def fits.src(s: TResolve.Src) -> Bool:
  match s:
    case TResolve.Src{c, st, b}:
      match st:
        case None{}:
          match b:
            case None{}:
              True{}
            case Some{f}:
              fits.file(f)
        case Some{x}:
          match b:
            case None{}:
              fits.str(x)
            case Some{f}:
              Bool.and(fits.str(x), fits.file(f))

def fits.srcs(ss: List<&2, TResolve.Src>) -> Bool:
  match ss:
    case Nil{}:
      True{}
    case s <> t:
      Bool.and(fits.src(s), fits.srcs(t))

# a request Rust writes: every text, count and index fits the wire
def fits(r: FTh.Req) -> Bool:
  match r:
    case FTh.Load{f}:
      fits.file(f)
    case FTh.Resolve{n, +ss}:
      Bool.and(fits.str(n), Bool.and(LawsBase.wire_fits(List.length(&2, TResolve.Src, ss)), fits.srcs(ss)))
    case FTh.Shipped{s}:
      True{}

# The color each token paints
# ---------------------------
# a written color is itself, an index its xterm-256 color; the terminal
# default (or a token past the palette) is the background (token 57) on a
# surface (tokens 48-57) and the foreground (58) elsewhere

def canvas(m: Maybe<&2, TFile.Val>) -> Co.Rgb:
  match m:
    case None{}:
      Co.Rgb{0, 0, 0}
    case Some{v}:
      match v:
        case TFile.Dflt{}:
          Co.Rgb{0, 0, 0}
        case TFile.Idx{i}:
          Co.Rgb{0, 0, 0}
        case TFile.Hex{c}:
          c

def paint.dflt(+vs: List<&2, TFile.Val>, surface: Bool) -> Co.Rgb:
  match surface:
    case True{}:
      canvas(List.get(&2, TFile.Val, vs, 57n))
    case False{}:
      canvas(List.get(&2, TFile.Val, vs, 58n))

def paint.of(+vs: List<&2, TFile.Val>, +t: U32, m: Maybe<&2, TFile.Val>) -> Co.Rgb:
  match m:
    case None{}:
      paint.dflt(vs, Bool.and(U32.is_ge(t, 48), U32.is_le(t, 57)))
    case Some{v}:
      match v:
        case TFile.Dflt{}:
          paint.dflt(vs, Bool.and(U32.is_ge(t, 48), U32.is_le(t, 57)))
        case TFile.Idx{i}:
          Co.ansi256(i)
        case TFile.Hex{c}:
          c

# the color token t paints in the palette vs (a value per token)
def paint(+vs: List<&2, TFile.Val>, +t: U32) -> Co.Rgb:
  paint.of(vs, t, List.get(&2, TFile.Val, vs, U32.to_nat(t)))

# the tokens 0-58, in order
def toks.go(k: Nat, +t: U32) -> List<&2, U32>:
  match k:
    case 0n:
      Nil{}
    case 1n+m:
      t <> toks.go(m, (t + 1 : U32))

def toks() -> List<&2, U32>:
  toks.go(59n, 0)

# Replies, as Rust reads them
# ---------------------------

def rgb(c: Co.Rgb, rest: String) -> String:
  match c:
    case Co.Rgb{r, g, b}:
      Wr.put_u32(r, Wr.put_u32(g, Wr.put_u32(b, rest)))

def rgbs.items(cs: List<&2, Co.Rgb>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      rgb(c, rgbs.items(t, rest))

def mrgb(m: Maybe<&2, Co.Rgb>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{c}:
      Wr.put_nat(1n, rgb(c, rest))

def val(v: TFile.Val, rest: String) -> String:
  match v:
    case TFile.Dflt{}:
      Wr.put_nat(0n, rest)
    case TFile.Idx{i}:
      Wr.put_nat(1n, Wr.put_u32(i, rest))
    case TFile.Hex{c}:
      Wr.put_nat(2n, rgb(c, rest))

def vals.items(vs: List<&2, TFile.Val>, rest: String) -> String:
  match vs:
    case Nil{}:
      rest
    case v <> t:
      val(v, vals.items(t, rest))

# the colors the tokens ts paint in vs
def paints.items(+vs: List<&2, TFile.Val>, ts: List<&2, U32>, rest: String) -> String:
  match ts:
    case Nil{}:
      rest
    case t <> u:
      rgb(paint(vs, t), paints.items(vs, u, rest))

def why(w: TFile.Why, rest: String) -> String:
  match w:
    case TFile.Circular{n}:
      Wr.put_nat(0n, Wr.put_str(n, rest))
    case TFile.NotFound{n}:
      Wr.put_nat(1n, Wr.put_str(n, rest))
    case TFile.BadHex{x}:
      Wr.put_nat(2n, Wr.put_str(x, rest))
    case TFile.BadValue{x}:
      Wr.put_nat(3n, Wr.put_str(x, rest))

def surf(a: TFile.Surf, rest: String) -> String:
  match a:
    case TFile.OnPage{}:
      Wr.put_nat(0n, rest)
    case TFile.OnCard{}:
      Wr.put_nat(1n, rest)
    case TFile.OnInfo{}:
      Wr.put_nat(2n, rest)

def u32s.items(ts: List<&2, U32>, rest: String) -> String:
  match ts:
    case Nil{}:
      rest
    case t <> u:
      Wr.put_u32(t, u32s.items(u, rest))

def fault(f: TFile.Fault, rest: String) -> String:
  match f:
    case TFile.Unknown{k}:
      Wr.put_nat(0n, Wr.put_str(k, rest))
    case TFile.InColor{k, w}:
      Wr.put_nat(1n, Wr.put_str(k, why(w, rest)))
    case TFile.Missing{+ts}:
      Wr.put_nat(2n, Wr.put_nat(List.length(&2, U32, ts), u32s.items(ts, rest)))
    case TFile.InExport{a, w}:
      Wr.put_nat(3n, surf(a, why(w, rest)))

# a parse: rejected and why; or painted: a value per token, the color each
# token paints, light or dark, the own #rrggbb background, the export page,
# card and info backgrounds
def parsed(p: TPalette.Parsed, rest: String) -> String:
  match p:
    case TPalette.Rejected{f}:
      Wr.put_nat(0n, fault(f, rest))
    case TPalette.Painted{+vs, l, d, pg, cd, io}:
      Wr.put_nat(1n, Wr.put_nat(List.length(&2, TFile.Val, vs), vals.items(vs, Wr.put_nat(59n, paints.items(vs, toks(), Wr.put_bool(l, mrgb(d, mrgb(pg, mrgb(cd, mrgb(io, rest))))))))))

def mparsed(m: Maybe<&2, TPalette.Parsed>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{p}:
      Wr.put_nat(1n, parsed(p, rest))

def mcause(m: Maybe<&2, TChoice.Cause>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(0n, rest)
    case Some{c}:
      match c:
        case TChoice.FailedAt{at}:
          Wr.put_nat(1n, Wr.put_nat(0n, Wr.put_nat(at, rest)))
        case TChoice.NoTheme{}:
          Wr.put_nat(1n, Wr.put_nat(1n, rest))

def clashes.items(cs: List<&2, TChoice.Clash>, rest: String) -> String:
  match cs:
    case Nil{}:
      rest
    case c <> t:
      match c:
        case TChoice.Clash{at, w}:
          Wr.put_nat(at, Wr.put_nat(w, clashes.items(t, rest)))

def nats.items(ns: List<&2, Nat>, rest: String) -> String:
  match ns:
    case Nil{}:
      rest
    case n <> t:
      Wr.put_nat(n, nats.items(t, rest))

# One load, as the laws state it
# ------------------------------

# a file's theme object read and completed (None: none)
def load(s: TResolve.Src) -> Maybe<&2, TPalette.Parsed>:
  match s:
    case TResolve.Src{c, st, b}:
      match b:
        case None{}:
          None{}
        case Some{f}:
          Some{TPalette.parse(f)}

def ld.parsed(c: Bool, st: Maybe<&2, String>, nm: String, p: TPalette.Parsed) -> TChoice.Ld:
  match p:
    case TPalette.Rejected{x}:
      TChoice.Broke{Some{nm}, st}
    case TPalette.Painted{a, l, d, pg, k, i}:
      TChoice.Fine{nm, c}

# a file as the pick sees it: valid by the name it advertises when its
# theme object completes; else broken, with that name when it has a theme
# object, and its stem
def ld(s: TResolve.Src) -> TChoice.Ld:
  match s:
    case TResolve.Src{c, st, b}:
      match b:
        case None{}:
          TChoice.Broke{None{}, st}
        case Some{f}:
          match f:
            case TFile.RFile{+nm, vs, es, pg, cd, io}:
              ld.parsed(c, st, nm, TPalette.parse(TFile.RFile{nm, vs, es, pg, cd, io}))

def lds(ss: List<&2, TResolve.Src>) -> List<&2, TChoice.Ld>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> t:
      ld(s) <> lds(t)

def out.of(m: Maybe<&2, TPalette.Parsed>, rest: String) -> String:
  match m:
    case None{}:
      Wr.put_nat(2n, rest)
    case Some{p}:
      match p:
        case TPalette.Rejected{x}:
          Wr.put_nat(1n, fault(x, rest))
        case TPalette.Painted{a, l, d, pg, k, i}:
          Wr.put_nat(0n, rest)

# how a file read: 0 loaded, 1 invalid and why, 2 no theme object
def out(s: TResolve.Src, rest: String) -> String:
  out.of(load(s), rest)

def outs.items(ss: List<&2, TResolve.Src>, rest: String) -> String:
  match ss:
    case Nil{}:
      rest
    case s <> t:
      out(s, outs.items(t, rest))

def load.got(m: Maybe<&2, TResolve.Src>) -> Maybe<&2, TPalette.Parsed>:
  match m:
    case None{}:
      None{}
    case Some{s}:
      load(s)

# the file at index k read and completed (None: no theme object, or no
# such file)
def load.at(ss: List<&2, TResolve.Src>, k: Nat) -> Maybe<&2, TPalette.Parsed>:
  load.got(List.get(&2, TResolve.Src, ss, k))

# equal values, compared field by field
def eq.rgb(a: Co.Rgb, b: Co.Rgb) -> Bool:
  match a b:
    case Co.Rgb{ar, ag, ab} Co.Rgb{br, bg, bb}:
      Bool.and(U32.is_eq(ar, br), Bool.and(U32.is_eq(ag, bg), U32.is_eq(ab, bb)))

def eq.val(a: TFile.Val, b: TFile.Val) -> Bool:
  match a:
    case TFile.Dflt{}:
      match b:
        case TFile.Dflt{}:
          True{}
        case TFile.Idx{j}:
          False{}
        case TFile.Hex{d}:
          False{}
    case TFile.Idx{i}:
      match b:
        case TFile.Dflt{}:
          False{}
        case TFile.Idx{j}:
          U32.is_eq(i, j)
        case TFile.Hex{d}:
          False{}
    case TFile.Hex{c}:
      match b:
        case TFile.Dflt{}:
          False{}
        case TFile.Idx{j}:
          False{}
        case TFile.Hex{d}:
          eq.rgb(c, d)

def eq.vals(a: List<&2, TFile.Val>, b: List<&2, TFile.Val>) -> Bool:
  match a:
    case Nil{}:
      match b:
        case Nil{}:
          True{}
        case y <> t:
          False{}
    case x <> s:
      match b:
        case Nil{}:
          False{}
        case y <> t:
          Bool.and(eq.val(x, y), eq.vals(s, t))

def eq.mrgb(a: Maybe<&2, Co.Rgb>, b: Maybe<&2, Co.Rgb>) -> Bool:
  match a:
    case None{}:
      match b:
        case None{}:
          True{}
        case Some{d}:
          False{}
    case Some{c}:
      match b:
        case None{}:
          False{}
        case Some{d}:
          eq.rgb(c, d)

def eq.bool(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

def same.parsed(a: TPalette.Parsed, b: TPalette.Parsed) -> Bool:
  match a:
    case TPalette.Rejected{x}:
      False{}
    case TPalette.Painted{va, la, da, pa, ca, ia}:
      match b:
        case TPalette.Rejected{y}:
          False{}
        case TPalette.Painted{vb, lb, db, pb, cb, ib}:
          Bool.and(eq.vals(va, vb), Bool.and(eq.bool(la, lb), Bool.and(eq.mrgb(da, db), Bool.and(eq.mrgb(pa, pb), Bool.and(eq.mrgb(ca, cb), eq.mrgb(ia, ib))))))

# two loaded files have the same palette: every value, light or dark, the
# own background, the export backgrounds
def same(a: Maybe<&2, TPalette.Parsed>, b: Maybe<&2, TPalette.Parsed>) -> Bool:
  match a:
    case None{}:
      False{}
    case Some{x}:
      match b:
        case None{}:
          False{}
        case Some{y}:
          same.parsed(x, y)

def warns.if(quiet: Bool, at: Nat, w: Nat, rest: List<&2, TChoice.Clash>) -> List<&2, TChoice.Clash>:
  match quiet:
    case True{}:
      rest
    case False{}:
      TChoice.Clash{at, w} <> rest

# the clashes whose palette differs from the winner's, in order
def warns(+ss: List<&2, TResolve.Src>, cs: List<&2, TChoice.Clash>) -> List<&2, TChoice.Clash>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> t:
      match c:
        case TChoice.Clash{+at, +w}:
          warns.if(same(load.at(ss, at), load.at(ss, w)), at, w, warns(ss, t))

def picked.if(low: Bool, +ss: List<&2, TResolve.Src>, +id: U32) -> Maybe<&2, TPalette.Parsed>:
  match low:
    case True{}:
      None{}
    case False{}:
      load.at(ss, U32.to_nat((id - 3 : U32)))

# the palette of the theme picked when it is a file (id 3 on)
def picked(+ss: List<&2, TResolve.Src>, +id: U32) -> Maybe<&2, TPalette.Parsed>:
  picked.if(U32.is_lt(id, 3), ss, id)

def answer.pick(+ss: List<&2, TResolve.Src>, p: TChoice.Pick) -> String:
  match p:
    case TChoice.Pick{r, c, +k, +b}:
      match r:
        case TName.Res{+id, w}:
          +ws = warns(ss, k)
          Wr.put_u32(id, Wr.put_bool(w, mcause(c, Wr.put_nat(List.length(&2, TChoice.Clash, ws), clashes.items(ws, Wr.put_nat(List.length(&2, Nat, b), nats.items(b, Wr.put_nat(List.length(&2, TResolve.Src, ss), outs.items(ss, mparsed(picked(ss, id), ""))))))))))

# the answer to a request: the file's parse; what the name picks over the
# files (TChoice.pick), the clashes that warn, the other files that did
# not load, how each file read and the picked file's palette; the shipped
# theme's colors
def answer(r: FTh.Req) -> String:
  match r:
    case FTh.Load{f}:
      parsed(TPalette.parse(f), "")
    case FTh.Resolve{+n, +ss}:
      answer.pick(ss, TChoice.pick(lds(ss), n))
    case FTh.Shipped{s}:
      +cs = TBundled.table(s)
      Wr.put_nat(List.length(&2, Co.Rgb, cs), rgbs.items(cs, ""))

