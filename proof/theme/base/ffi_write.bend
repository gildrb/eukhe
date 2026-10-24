# eukhe: lemmas of the theme entry's proofs: the entry's reply writers
# write what the laws' spellers (spec/theme_wire.bend) write, and each
# token paints the color the laws state

import Base
import ../../../bend/wire.bend as Wr
import ../../../bend/color.bend as Co
import ../../../bend/theme/file.bend as TFile
import ../../../bend/theme/token.bend as TToken
import ../../../bend/theme/palette.bend as TPalette
import ../../../bend/theme/choice.bend as TChoice
import ../../../bend/ffi_theme.bend as FTh
import ../../../spec/theme_wire.bend as Tw

# Colors and values
# -----------------

def tw.rgb(c: Co.Rgb, rest: String) -> {FTh.put_rgb(c, rest) == Tw.rgb(c, rest) : String}:
  match c:
    case Co.Rgb{r, g, b}:
      {==}

def tw.rgbs(cs: List<&2, Co.Rgb>, +rest: String) -> {FTh.put_rgbs.items(cs, rest) == Tw.rgbs.items(cs, rest) : String}:
  match cs:
    case Nil{}:
      {==}
    case +c <> +t:
      %tw.rgbs(t, rest) : {FTh.put_rgb(c, FTh.put_rgbs.items(t, rest)) == Tw.rgb(c, _) : String}
      tw.rgb(c, FTh.put_rgbs.items(t, rest))

def tw.mrgb(m: Maybe<&2, Co.Rgb>, rest: String) -> {FTh.put_mrgb(m, rest) == Tw.mrgb(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{c}:
      match c:
        case Co.Rgb{r, g, b}:
          {==}

def tw.val(v: TFile.Val, rest: String) -> {FTh.put_val(v, rest) == Tw.val(v, rest) : String}:
  match v:
    case TFile.Dflt{}:
      {==}
    case TFile.Idx{i}:
      {==}
    case TFile.Hex{c}:
      match c:
        case Co.Rgb{r, g, b}:
          {==}

def tw.vals(vs: List<&2, TFile.Val>, +rest: String) -> {FTh.put_vals.items(vs, rest) == Tw.vals.items(vs, rest) : String}:
  match vs:
    case Nil{}:
      {==}
    case +v <> +t:
      %tw.vals(t, rest) : {FTh.put_val(v, FTh.put_vals.items(t, rest)) == Tw.val(v, _) : String}
      tw.val(v, FTh.put_vals.items(t, rest))

# Why a file is invalid
# ---------------------

def tw.why(w: TFile.Why, rest: String) -> {FTh.put_why(w, rest) == Tw.why(w, rest) : String}:
  match w:
    case TFile.Circular{n}:
      {==}
    case TFile.NotFound{n}:
      {==}
    case TFile.BadHex{x}:
      {==}
    case TFile.BadValue{x}:
      {==}

def tw.surf(a: TFile.Surf, rest: String) -> {FTh.put_surf(a, rest) == Tw.surf(a, rest) : String}:
  match a:
    case TFile.OnPage{}:
      {==}
    case TFile.OnCard{}:
      {==}
    case TFile.OnInfo{}:
      {==}

def tw.toks(ts: List<&2, U32>, -rest: String) -> {FTh.put_toks.items(ts, rest) == Tw.u32s.items(ts, rest) : String}:
  match ts:
    case Nil{}:
      {==}
    case +t <> u:
      %tw.toks(u, rest) : {Wr.put_u32(t, FTh.put_toks.items(u, rest)) == Wr.put_u32(t, _) : String}
      {==}

def tw.fault(f: TFile.Fault, +rest: String) -> {FTh.put_fault(f, rest) == Tw.fault(f, rest) : String}:
  match f:
    case TFile.Unknown{k}:
      {==}
    case TFile.InColor{+k, +w}:
      %tw.why(w, rest) : {Wr.put_nat(1n, Wr.put_str(k, FTh.put_why(w, rest))) == Wr.put_nat(1n, Wr.put_str(k, _)) : String}
      {==}
    case TFile.Missing{+ts}:
      %tw.toks(ts, rest) : {Wr.put_nat(2n, Wr.put_nat(List.length(&2, U32, ts), FTh.put_toks.items(ts, rest))) == Wr.put_nat(2n, Wr.put_nat(List.length(&2, U32, ts), _)) : String}
      {==}
    case TFile.InExport{+a, +w}:
      %tw.why(w, rest) : {Wr.put_nat(3n, FTh.put_surf(a, FTh.put_why(w, rest))) == Wr.put_nat(3n, Tw.surf(a, _)) : String}
      %tw.surf(a, FTh.put_why(w, rest)) : {Wr.put_nat(3n, FTh.put_surf(a, FTh.put_why(w, rest))) == Wr.put_nat(3n, _) : String}
      {==}

# The color each token paints
# ---------------------------

# a value of the palette as somes holds it
def tw.lift(m: Maybe<&2, TFile.Val>) -> Maybe<&2, Maybe<&2, TFile.Val>>:
  match m:
    case None{}:
      None{}
    case Some{v}:
      Some{Some{v}}

# token k of somes(vs) is token k of vs, lifted
def tw.get(vs: List<&2, TFile.Val>, k: Nat) -> {tw.lift(List.get(&2, TFile.Val, vs, k)) == List.get(&2, Maybe<&2, TFile.Val>, FTh.somes(vs), k) : Maybe<&2, Maybe<&2, TFile.Val>>}:
  match vs k:
    case Nil{} _:
      {==}
    case v <> t 0n:
      {==}
    case v <> t 1n+p:
      tw.get(t, p)

def tw.canvas_of(m: Maybe<&2, TFile.Val>) -> {TPalette.paint.hex(TPalette.or_else(TFile.Val, TPalette.or_else(Maybe<&2, TFile.Val>, tw.lift(m), None{}), TFile.Dflt{})) == Tw.canvas(m) : Co.Rgb}:
  match m:
    case None{}:
      {==}
    case Some{v}:
      match v:
        case TFile.Dflt{}:
          {==}
        case TFile.Idx{i}:
          {==}
        case TFile.Hex{c}:
          {==}

def tw.canvas(+vs: List<&2, TFile.Val>, b: Bool) -> {TPalette.paint.canvas(FTh.somes(vs), b) == Tw.paint.dflt(vs, b) : Co.Rgb}:
  match b:
    case True{}:
      %tw.get(vs, 57n) : {TPalette.paint.hex(TPalette.or_else(TFile.Val, TPalette.or_else(Maybe<&2, TFile.Val>, _, None{}), TFile.Dflt{})) == Tw.canvas(List.get(&2, TFile.Val, vs, 57n)) : Co.Rgb}
      tw.canvas_of(List.get(&2, TFile.Val, vs, 57n))
    case False{}:
      %tw.get(vs, 58n) : {TPalette.paint.hex(TPalette.or_else(TFile.Val, TPalette.or_else(Maybe<&2, TFile.Val>, _, None{}), TFile.Dflt{})) == Tw.canvas(List.get(&2, TFile.Val, vs, 58n)) : Co.Rgb}
      tw.canvas_of(List.get(&2, TFile.Val, vs, 58n))

def tw.paint_of(+vs: List<&2, TFile.Val>, +t: U32, m: Maybe<&2, TFile.Val>) -> {TPalette.paint.val(FTh.somes(vs), t, TPalette.or_else(TFile.Val, TPalette.or_else(Maybe<&2, TFile.Val>, tw.lift(m), None{}), TFile.Dflt{})) == Tw.paint.of(vs, t, m) : Co.Rgb}:
  match m:
    case None{}:
      tw.canvas(vs, Bool.and(U32.is_ge(t, 48), U32.is_le(t, 57)))
    case Some{v}:
      match v:
        case TFile.Dflt{}:
          tw.canvas(vs, Bool.and(U32.is_ge(t, 48), U32.is_le(t, 57)))
        case TFile.Idx{i}:
          {==}
        case TFile.Hex{c}:
          {==}

# token t paints in the entry what the laws say it paints
def tw.paint(+vs: List<&2, TFile.Val>, +t: U32) -> {TPalette.paint(FTh.somes(vs), t) == Tw.paint(vs, t) : Co.Rgb}:
  %tw.get(vs, U32.to_nat(t)) : {TPalette.paint.val(FTh.somes(vs), t, TPalette.or_else(TFile.Val, TPalette.or_else(Maybe<&2, TFile.Val>, _, None{}), TFile.Dflt{})) == Tw.paint(vs, t) : Co.Rgb}
  tw.paint_of(vs, t, List.get(&2, TFile.Val, vs, U32.to_nat(t)))

def tw.paints(+vs: List<&2, TFile.Val>, ts: List<&2, U32>, +rest: String) -> {FTh.put_rgbs.items(FTh.paints(FTh.somes(vs), ts), rest) == Tw.paints.items(vs, ts, rest) : String}:
  match ts:
    case Nil{}:
      {==}
    case +t <> +u:
      %tw.paints(vs, u, rest) : {FTh.put_rgb(TPalette.paint(FTh.somes(vs), t), FTh.put_rgbs.items(FTh.paints(FTh.somes(vs), u), rest)) == Tw.rgb(Tw.paint(vs, t), _) : String}
      %tw.paint(vs, t) : {FTh.put_rgb(TPalette.paint(FTh.somes(vs), t), FTh.put_rgbs.items(FTh.paints(FTh.somes(vs), u), rest)) == Tw.rgb(_, FTh.put_rgbs.items(FTh.paints(FTh.somes(vs), u), rest)) : String}
      tw.rgb(TPalette.paint(FTh.somes(vs), t), FTh.put_rgbs.items(FTh.paints(FTh.somes(vs), u), rest))

# Parses
# ------

def tw.parsed(p: TPalette.Parsed, +rest: String) -> {FTh.put_parsed(p, rest) == Tw.parsed(p, rest) : String}:
  match p:
    case TPalette.Rejected{f}:
      %tw.fault(f, rest) : {Wr.put_nat(0n, FTh.put_fault(f, rest)) == Wr.put_nat(0n, _) : String}
      {==}
    case TPalette.Painted{+vs, +l, +d, +pg, +cd, +io}:
      +r4 = FTh.put_mrgb(io, rest)
      +r3 = FTh.put_mrgb(cd, r4)
      +r2 = FTh.put_mrgb(pg, r3)
      +r1 = FTh.put_mrgb(d, r2)
      %tw.mrgb(io, rest) : {Wr.put_nat(1n, Wr.put_nat(List.length(&2, TFile.Val, vs), FTh.put_vals.items(vs, Wr.put_nat(59n, FTh.put_rgbs.items(FTh.paints(FTh.somes(vs), TToken.toks()), Wr.put_bool(l, r1)))))) == Wr.put_nat(1n, Wr.put_nat(List.length(&2, TFile.Val, vs), Tw.vals.items(vs, Wr.put_nat(59n, Tw.paints.items(vs, Tw.toks(), Wr.put_bool(l, Tw.mrgb(d, Tw.mrgb(pg, Tw.mrgb(cd, _))))))))) : String}
      %tw.mrgb(cd, r4) : {Wr.put_nat(1n, Wr.put_nat(List.length(&2, TFile.Val, vs), FTh.put_vals.items(vs, Wr.put_nat(59n, FTh.put_rgbs.items(FTh.paints(FTh.somes(vs), TToken.toks()), Wr.put_bool(l, r1)))))) == Wr.put_nat(1n, Wr.put_nat(List.length(&2, TFile.Val, vs), Tw.vals.items(vs, Wr.put_nat(59n, Tw.paints.items(vs, Tw.toks(), Wr.put_bool(l, Tw.mrgb(d, Tw.mrgb(pg, _)))))))) : String}
      %tw.mrgb(pg, r3) : {Wr.put_nat(1n, Wr.put_nat(List.length(&2, TFile.Val, vs), FTh.put_vals.items(vs, Wr.put_nat(59n, FTh.put_rgbs.items(FTh.paints(FTh.somes(vs), TToken.toks()), Wr.put_bool(l, r1)))))) == Wr.put_nat(1n, Wr.put_nat(List.length(&2, TFile.Val, vs), Tw.vals.items(vs, Wr.put_nat(59n, Tw.paints.items(vs, Tw.toks(), Wr.put_bool(l, Tw.mrgb(d, _))))))) : String}
      %tw.mrgb(d, r2) : {Wr.put_nat(1n, Wr.put_nat(List.length(&2, TFile.Val, vs), FTh.put_vals.items(vs, Wr.put_nat(59n, FTh.put_rgbs.items(FTh.paints(FTh.somes(vs), TToken.toks()), Wr.put_bool(l, r1)))))) == Wr.put_nat(1n, Wr.put_nat(List.length(&2, TFile.Val, vs), Tw.vals.items(vs, Wr.put_nat(59n, Tw.paints.items(vs, Tw.toks(), Wr.put_bool(l, _)))))) : String}
      %tw.paints(vs, TToken.toks(), Wr.put_bool(l, r1)) : {Wr.put_nat(1n, Wr.put_nat(List.length(&2, TFile.Val, vs), FTh.put_vals.items(vs, Wr.put_nat(59n, FTh.put_rgbs.items(FTh.paints(FTh.somes(vs), TToken.toks()), Wr.put_bool(l, r1)))))) == Wr.put_nat(1n, Wr.put_nat(List.length(&2, TFile.Val, vs), Tw.vals.items(vs, Wr.put_nat(59n, _)))) : String}
      %tw.vals(vs, Wr.put_nat(59n, FTh.put_rgbs.items(FTh.paints(FTh.somes(vs), TToken.toks()), Wr.put_bool(l, r1)))) : {Wr.put_nat(1n, Wr.put_nat(List.length(&2, TFile.Val, vs), FTh.put_vals.items(vs, Wr.put_nat(59n, FTh.put_rgbs.items(FTh.paints(FTh.somes(vs), TToken.toks()), Wr.put_bool(l, r1)))))) == Wr.put_nat(1n, Wr.put_nat(List.length(&2, TFile.Val, vs), _)) : String}
      {==}

def tw.mparsed(m: Maybe<&2, TPalette.Parsed>, +rest: String) -> {FTh.put_mparsed(m, rest) == Tw.mparsed(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{+p}:
      %tw.parsed(p, rest) : {Wr.put_nat(1n, FTh.put_parsed(p, rest)) == Wr.put_nat(1n, _) : String}
      {==}

# The pick
# --------

def tw.mcause(m: Maybe<&2, TChoice.Cause>, rest: String) -> {FTh.put_mcause(m, rest) == Tw.mcause(m, rest) : String}:
  match m:
    case None{}:
      {==}
    case Some{c}:
      match c:
        case TChoice.FailedAt{at}:
          {==}
        case TChoice.NoTheme{}:
          {==}

def tw.clashes(cs: List<&2, TChoice.Clash>, -rest: String) -> {FTh.put_clashes.items(cs, rest) == Tw.clashes.items(cs, rest) : String}:
  match cs:
    case Nil{}:
      {==}
    case c <> t:
      match c:
        case TChoice.Clash{+at, +w}:
          %tw.clashes(t, rest) : {Wr.put_nat(at, Wr.put_nat(w, FTh.put_clashes.items(t, rest))) == Wr.put_nat(at, Wr.put_nat(w, _)) : String}
          {==}

def tw.nats(ns: List<&2, Nat>, -rest: String) -> {FTh.put_nats.items(ns, rest) == Tw.nats.items(ns, rest) : String}:
  match ns:
    case Nil{}:
      {==}
    case +n <> t:
      %tw.nats(t, rest) : {Wr.put_nat(n, FTh.put_nats.items(t, rest)) == Wr.put_nat(n, _) : String}
      {==}
