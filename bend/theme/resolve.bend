# theme: one load: every file the sources reach read and completed, the theme a name picks over them, the clashes that warn, and the picked file's palette

import Base
import ../color.bend as Co
import ./file.bend as TFile
import ./palette.bend as TPalette
import ./choice.bend as TChoice
import ./name.bend as TName

# Rust reads every file the sources reach (the registered files, then the
# custom directory's), in that order, and decodes the JSON of each;
# `resolve` decides the rest in one call.

# a file the sources reach: from the custom directory or not, its file
# stem when that is text, and its theme object (None: the file could not
# be read, or is no theme object)
type Src is Data:
  Src{custom: Bool, stem: Maybe<&2, String>, body: Maybe<&2, TFile.RFile>}

# a file read: no theme object, or the name it advertises and the file
# read and completed
type Read is Data:
  NoBody{}
  Body{name: String, p: TPalette.Parsed}

def name.of(f: TFile.RFile) -> String:
  match f:
    case TFile.RFile{nm, vars, cols, page, card, info}:
      nm

def read.of(m: Maybe<&2, TFile.RFile>) -> Read:
  match m:
    case None{}:
      NoBody{}
    case Some{+f}:
      Body{name.of(f), TPalette.parse(f)}

# the file as the pick sees it: valid by the name it advertises, or
# broken with that name (when it is a theme object) and its stem
def ld.body(custom: Bool, stem: Maybe<&2, String>, nm: String, p: TPalette.Parsed) -> TChoice.Ld:
  match p:
    case TPalette.Rejected{f}:
      TChoice.Broke{Some{nm}, stem}
    case TPalette.Painted{vs, l, d, pg, cd, io}:
      TChoice.Fine{nm, custom}

def ld.of(custom: Bool, stem: Maybe<&2, String>, r: Read) -> TChoice.Ld:
  match r:
    case NoBody{}:
      TChoice.Broke{None{}, stem}
    case Body{nm, p}:
      ld.body(custom, stem, nm, p)

# a file seen: as the pick sees it, and as it read
type Seen is Data:
  Seen{ld: TChoice.Ld, r: Read}

def seen(s: Src) -> Seen:
  match s:
    case Src{custom, stem, body}:
      +r = read.of(body)
      Seen{ld.of(custom, stem, r), r}

def seens(ss: List<&2, Src>) -> List<&2, Seen>:
  match ss:
    case Nil{}:
      Nil{}
    case s <> rest:
      seen(s) <> seens(rest)

def lds(xs: List<&2, Seen>) -> List<&2, TChoice.Ld>:
  match xs:
    case Nil{}:
      Nil{}
    case Seen{l, r} <> rest:
      l <> lds(rest)

# Outcomes
# --------

# how a file read: loaded, invalid (and why), or no theme object
type Out is Data:
  OLoaded{}
  OFaulty{f: TFile.Fault}
  ONone{}

def out.parsed(p: TPalette.Parsed) -> Out:
  match p:
    case TPalette.Rejected{f}:
      OFaulty{f}
    case TPalette.Painted{vs, l, d, pg, cd, io}:
      OLoaded{}

def out(r: Read) -> Out:
  match r:
    case NoBody{}:
      ONone{}
    case Body{nm, p}:
      out.parsed(p)

def outs(xs: List<&2, Seen>) -> List<&2, Out>:
  match xs:
    case Nil{}:
      Nil{}
    case Seen{l, r} <> rest:
      out(r) <> outs(rest)

# The palettes of the files
# -------------------------

def parsed.of(r: Read) -> Maybe<&2, TPalette.Parsed>:
  match r:
    case NoBody{}:
      None{}
    case Body{nm, p}:
      Some{p}

def parsed.seen(x: Seen) -> Maybe<&2, TPalette.Parsed>:
  match x:
    case Seen{l, r}:
      parsed.of(r)

# the file at index at, read and completed (None: no theme object, or no
# such file)
def parsed.at(xs: List<&2, Seen>, at: Nat) -> Maybe<&2, TPalette.Parsed>:
  match xs at:
    case Nil{} _:
      None{}
    case x <> rest 0n:
      parsed.seen(x)
    case x <> rest 1n+p:
      parsed.at(rest, p)

def same.val(a: TFile.Val, b: TFile.Val) -> Bool:
  match a b:
    case TFile.Dflt{} TFile.Dflt{}:
      True{}
    case TFile.Dflt{} TFile.Idx{j}:
      False{}
    case TFile.Dflt{} TFile.Hex{d}:
      False{}
    case TFile.Idx{i} TFile.Dflt{}:
      False{}
    case TFile.Idx{i} TFile.Idx{j}:
      U32.is_eq(i, j)
    case TFile.Idx{i} TFile.Hex{d}:
      False{}
    case TFile.Hex{c} TFile.Dflt{}:
      False{}
    case TFile.Hex{c} TFile.Idx{j}:
      False{}
    case TFile.Hex{c} TFile.Hex{d}:
      Co.eq(c, d)

def same.vals(a: List<&2, TFile.Val>, b: List<&2, TFile.Val>) -> Bool:
  match a b:
    case Nil{} Nil{}:
      True{}
    case Nil{} Con{y, t}:
      False{}
    case Con{x, s} Nil{}:
      False{}
    case Con{x, s} Con{y, t}:
      Bool.and(same.val(x, y), same.vals(s, t))

def same.rgb(a: Maybe<&2, Co.Rgb>, b: Maybe<&2, Co.Rgb>) -> Bool:
  match a b:
    case None{} None{}:
      True{}
    case None{} Some{d}:
      False{}
    case Some{c} None{}:
      False{}
    case Some{c} Some{d}:
      Co.eq(c, d)

def same.bool(a: Bool, b: Bool) -> Bool:
  match a:
    case True{}:
      b
    case False{}:
      Bool.not(b)

# two palettes are the same: every value, the mode, the own background
# and the export backgrounds
def same.painted(a: TPalette.Parsed, b: TPalette.Parsed) -> Bool:
  match a b:
    case TPalette.Painted{va, la, da, pa, ca, ia} TPalette.Painted{vb, lb, db, pb, cb, ib}:
      Bool.and(same.vals(va, vb), Bool.and(same.bool(la, lb), Bool.and(same.rgb(da, db), Bool.and(same.rgb(pa, pb), Bool.and(same.rgb(ca, cb), same.rgb(ia, ib))))))
    case TPalette.Painted{va, la, da, pa, ca, ia} TPalette.Rejected{g}:
      False{}
    case TPalette.Rejected{f} TPalette.Painted{vb, lb, db, pb, cb, ib}:
      False{}
    case TPalette.Rejected{f} TPalette.Rejected{g}:
      False{}

def same.at(a: Maybe<&2, TPalette.Parsed>, b: Maybe<&2, TPalette.Parsed>) -> Bool:
  match a b:
    case None{} None{}:
      False{}
    case None{} Some{y}:
      False{}
    case Some{x} None{}:
      False{}
    case Some{x} Some{y}:
      same.painted(x, y)

# A clash warns only when its palette differs from the winner's: the same
# theme twice (a config mirrored into a project, a copy) loses silently.

def warns.keep(quiet: Bool, c: TChoice.Clash, rest: List<&2, TChoice.Clash>) -> List<&2, TChoice.Clash>:
  match quiet:
    case True{}:
      rest
    case False{}:
      c <> rest

def warns.clash(+xs: List<&2, Seen>, c: TChoice.Clash, rest: List<&2, TChoice.Clash>) -> List<&2, TChoice.Clash>:
  match c:
    case TChoice.Clash{+at, +w}:
      warns.keep(same.at(parsed.at(xs, at), parsed.at(xs, w)), TChoice.Clash{at, w}, rest)

def warns(+xs: List<&2, Seen>, cs: List<&2, TChoice.Clash>) -> List<&2, TChoice.Clash>:
  match cs:
    case Nil{}:
      Nil{}
    case c <> rest:
      warns.clash(xs, c, warns(xs, rest))

# the palette of the theme picked, when it is a file (ids 3 on; the
# builtins 0..2 are Rust's bundled files)
def picked.at(+xs: List<&2, Seen>, low: Bool, +id: U32) -> Maybe<&2, TPalette.Parsed>:
  match low:
    case True{}:
      None{}
    case False{}:
      parsed.at(xs, U32.to_nat((id - 3 : U32)))

def picked(+xs: List<&2, Seen>, +id: U32) -> Maybe<&2, TPalette.Parsed>:
  picked.at(xs, U32.is_lt(id, 3), id)

# One load
# --------

# what a name resolves to over the files: the pick (TChoice.pick) with
# only the clashes that warn, how each file read, and the picked file's
# palette
type Resolved is Data:
  Resolved{res: TName.Res, cause: Maybe<&2, TChoice.Cause>, clashes: List<&2, TChoice.Clash>, broken: List<&2, Nat>, outs: List<&2, Out>, picked: Maybe<&2, TPalette.Parsed>}

def resolve.res(+xs: List<&2, Seen>, r: TName.Res, c: Maybe<&2, TChoice.Cause>, k: List<&2, TChoice.Clash>, b: List<&2, Nat>) -> Resolved:
  match r:
    case TName.Res{+id, w}:
      Resolved{TName.Res{id, w}, c, warns(xs, k), b, outs(xs), picked(xs, id)}

def resolve.pick(+xs: List<&2, Seen>, p: TChoice.Pick) -> Resolved:
  match p:
    case TChoice.Pick{r, c, k, b}:
      resolve.res(xs, r, c, k, b)

# resolve name n over the files ss
def resolve(+n: String, ss: List<&2, Src>) -> Resolved:
  +xs = seens(ss)
  resolve.pick(xs, TChoice.pick(lds(xs), n))
