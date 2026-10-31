# eukhe: lemmas of the theme entry's proofs: one load of the model
# (bend/theme/resolve.bend) is the load the laws state
# (spec/theme/wire.bend): the files as the pick sees them, how each file
# read, the file at an index, the same-palette test, the clashes that warn
# and the picked file; and the entry spells that load as the laws do

import Base
import ../../../bend/wire.bend as Wr
import ../../../bend/color.bend as Co
import ../../../bend/theme/file.bend as TFile
import ../../../bend/theme/palette.bend as TPalette
import ../../../bend/theme/choice.bend as TChoice
import ../../../bend/theme/name.bend as TName
import ../../../bend/theme/resolve.bend as TResolve
import ../../../bend/ffi_theme.bend as FTh
import ../../../spec/theme/wire.bend as Tw
import ./ffi_write.bend as LTWrite

# The files as the pick sees them
# -------------------------------

def tv.ldp(c: Bool, st: Maybe<&2, String>, nm: String, p: TPalette.Parsed) -> {TResolve.ld.body(c, st, nm, p) == Tw.ld.parsed(c, st, nm, p) : TChoice.Ld}:
  match p:
    case TPalette.Rejected{x}:
      {==}
    case TPalette.Painted{a, l, d, pg, k, i}:
      {==}

def tv.ld(+c: Bool, +st: Maybe<&2, String>, b: Maybe<&2, TFile.RFile>) -> {TResolve.ld.of(c, st, TResolve.read.of(b)) == Tw.ld(TResolve.Src{c, st, b}) : TChoice.Ld}:
  match b:
    case None{}:
      {==}
    case Some{f}:
      match f:
        case TFile.RFile{+nm, +vs, +es, +pg, +cd, +io}:
          tv.ldp(c, st, nm, TPalette.parse(TFile.RFile{nm, vs, es, pg, cd, io}))

def tv.lds(ss: List<&2, TResolve.Src>) -> {TResolve.lds(TResolve.seens(ss)) == Tw.lds(ss) : List<&2, TChoice.Ld>}:
  match ss:
    case Nil{}:
      {==}
    case s <> t:
      match s:
        case TResolve.Src{+c, +st, +b}:
          %tv.lds(t) : {TResolve.ld.of(c, st, TResolve.read.of(b)) <> TResolve.lds(TResolve.seens(t)) == Tw.ld(TResolve.Src{c, st, b}) <> _ : List<&2, TChoice.Ld>}
          %tv.ld(c, st, b) : {TResolve.ld.of(c, st, TResolve.read.of(b)) <> TResolve.lds(TResolve.seens(t)) == _ <> TResolve.lds(TResolve.seens(t)) : List<&2, TChoice.Ld>}
          {==}

# How each file read
# ------------------

def tv.outp(p: TPalette.Parsed, +rest: String) -> {FTh.put_out(TResolve.out.parsed(p), rest) == Tw.out.of(Some{p}, rest) : String}:
  match p:
    case TPalette.Rejected{+x}:
      %LTWrite.tw.fault(x, rest) : {Wr.put_nat(1n, FTh.put_fault(x, rest)) == Wr.put_nat(1n, _) : String}
      {==}
    case TPalette.Painted{a, l, d, pg, k, i}:
      {==}

def tv.out(c: Bool, st: Maybe<&2, String>, b: Maybe<&2, TFile.RFile>, +rest: String) -> {FTh.put_out(TResolve.out(TResolve.read.of(b)), rest) == Tw.out.of(Tw.load(TResolve.Src{c, st, b}), rest) : String}:
  match b:
    case None{}:
      {==}
    case Some{+f}:
      tv.outp(TPalette.parse(f), rest)

def tv.outs(ss: List<&2, TResolve.Src>, +rest: String) -> {FTh.put_outs.items(TResolve.outs(TResolve.seens(ss)), rest) == Tw.outs.items(ss, rest) : String}:
  match ss:
    case Nil{}:
      {==}
    case s <> +t:
      match s:
        case TResolve.Src{+c, +st, +b}:
          %tv.outs(t, rest) : {FTh.put_out(TResolve.out(TResolve.read.of(b)), FTh.put_outs.items(TResolve.outs(TResolve.seens(t)), rest)) == Tw.out(TResolve.Src{c, st, b}, _) : String}
          tv.out(c, st, b, FTh.put_outs.items(TResolve.outs(TResolve.seens(t)), rest))

def tv.outs_len(ss: List<&2, TResolve.Src>) -> {List.length(&2, TResolve.Out, TResolve.outs(TResolve.seens(ss))) == List.length(&2, TResolve.Src, ss) : Nat}:
  match ss:
    case Nil{}:
      {==}
    case s <> t:
      match s:
        case TResolve.Src{c, st, b}:
          %tv.outs_len(t) : {1n+List.length(&2, TResolve.Out, TResolve.outs(TResolve.seens(t))) == 1n+_ : Nat}
          {==}

# The file at an index
# --------------------

def tv.at0(s: TResolve.Src, t: List<&2, TResolve.Src>) -> {TResolve.parsed.at(TResolve.seens(s <> t), 0n) == Tw.load.at(s <> t, 0n) : Maybe<&2, TPalette.Parsed>}:
  match s:
    case TResolve.Src{c, st, b}:
      match b:
        case None{}:
          {==}
        case Some{f}:
          {==}

def tv.at(ss: List<&2, TResolve.Src>, k: Nat) -> {TResolve.parsed.at(TResolve.seens(ss), k) == Tw.load.at(ss, k) : Maybe<&2, TPalette.Parsed>}:
  match ss k:
    case Nil{} _:
      {==}
    case s <> t 0n:
      tv.at0(s, t)
    case s <> t 1n+p:
      tv.at(t, p)

# The same palette
# ----------------

def tv.rgb(a: Co.Rgb, b: Co.Rgb) -> {Co.eq(a, b) == Tw.eq.rgb(a, b) : Bool}:
  match a b:
    case Co.Rgb{ar, ag, ab} Co.Rgb{br, bg, bb}:
      {==}

def tv.val(a: TFile.Val, b: TFile.Val) -> {TResolve.same.val(a, b) == Tw.eq.val(a, b) : Bool}:
  match a b:
    case TFile.Dflt{} TFile.Dflt{}:
      {==}
    case TFile.Dflt{} TFile.Idx{j}:
      {==}
    case TFile.Dflt{} TFile.Hex{d}:
      {==}
    case TFile.Idx{i} TFile.Dflt{}:
      {==}
    case TFile.Idx{i} TFile.Idx{j}:
      {==}
    case TFile.Idx{i} TFile.Hex{d}:
      {==}
    case TFile.Hex{c} TFile.Dflt{}:
      {==}
    case TFile.Hex{c} TFile.Idx{j}:
      {==}
    case TFile.Hex{c} TFile.Hex{d}:
      tv.rgb(c, d)

def tv.vals(a: List<&2, TFile.Val>, b: List<&2, TFile.Val>) -> {TResolve.same.vals(a, b) == Tw.eq.vals(a, b) : Bool}:
  match a b:
    case Nil{} Nil{}:
      {==}
    case Nil{} Con{y, t}:
      {==}
    case Con{x, s} Nil{}:
      {==}
    case Con{+x, +s} Con{+y, +t}:
      %tv.vals(s, t) : {Bool.and(TResolve.same.val(x, y), TResolve.same.vals(s, t)) == Bool.and(Tw.eq.val(x, y), _) : Bool}
      %tv.val(x, y) : {Bool.and(TResolve.same.val(x, y), TResolve.same.vals(s, t)) == Bool.and(_, TResolve.same.vals(s, t)) : Bool}
      {==}

def tv.mrgb(a: Maybe<&2, Co.Rgb>, b: Maybe<&2, Co.Rgb>) -> {TResolve.same.rgb(a, b) == Tw.eq.mrgb(a, b) : Bool}:
  match a b:
    case None{} None{}:
      {==}
    case None{} Some{d}:
      {==}
    case Some{c} None{}:
      {==}
    case Some{c} Some{d}:
      tv.rgb(c, d)

def tv.bool(a: Bool, b: Bool) -> {TResolve.same.bool(a, b) == Tw.eq.bool(a, b) : Bool}:
  match a:
    case True{}:
      {==}
    case False{}:
      {==}

def tv.painted(a: TPalette.Parsed, b: TPalette.Parsed) -> {TResolve.same.painted(a, b) == Tw.same.parsed(a, b) : Bool}:
  match a b:
    case TPalette.Painted{+va, +la, +da, +pa, +ca, +ia} TPalette.Painted{+vb, +lb, +db, +pb, +cb, +ib}:
      +x6 = TResolve.same.rgb(ia, ib)
      +x5 = Bool.and(TResolve.same.rgb(ca, cb), x6)
      +x4 = Bool.and(TResolve.same.rgb(pa, pb), x5)
      +x3 = Bool.and(TResolve.same.rgb(da, db), x4)
      +x2 = Bool.and(TResolve.same.bool(la, lb), x3)
      +x1 = Bool.and(TResolve.same.vals(va, vb), x2)
      %tv.mrgb(ia, ib) : {x1 == Bool.and(Tw.eq.vals(va, vb), Bool.and(Tw.eq.bool(la, lb), Bool.and(Tw.eq.mrgb(da, db), Bool.and(Tw.eq.mrgb(pa, pb), Bool.and(Tw.eq.mrgb(ca, cb), _))))) : Bool}
      %tv.mrgb(ca, cb) : {x1 == Bool.and(Tw.eq.vals(va, vb), Bool.and(Tw.eq.bool(la, lb), Bool.and(Tw.eq.mrgb(da, db), Bool.and(Tw.eq.mrgb(pa, pb), Bool.and(_, x6))))) : Bool}
      %tv.mrgb(pa, pb) : {x1 == Bool.and(Tw.eq.vals(va, vb), Bool.and(Tw.eq.bool(la, lb), Bool.and(Tw.eq.mrgb(da, db), Bool.and(_, x5)))) : Bool}
      %tv.mrgb(da, db) : {x1 == Bool.and(Tw.eq.vals(va, vb), Bool.and(Tw.eq.bool(la, lb), Bool.and(_, x4))) : Bool}
      %tv.bool(la, lb) : {x1 == Bool.and(Tw.eq.vals(va, vb), Bool.and(_, x3)) : Bool}
      %tv.vals(va, vb) : {x1 == Bool.and(_, x2) : Bool}
      {==}
    case TPalette.Painted{va, la, da, pa, ca, ia} TPalette.Rejected{y}:
      {==}
    case TPalette.Rejected{x} TPalette.Painted{vb, lb, db, pb, cb, ib}:
      {==}
    case TPalette.Rejected{x} TPalette.Rejected{y}:
      {==}

def tv.same(a: Maybe<&2, TPalette.Parsed>, b: Maybe<&2, TPalette.Parsed>) -> {TResolve.same.at(a, b) == Tw.same(a, b) : Bool}:
  match a b:
    case None{} None{}:
      {==}
    case None{} Some{y}:
      {==}
    case Some{x} None{}:
      {==}
    case Some{x} Some{y}:
      tv.painted(x, y)

# The clashes that warn
# ---------------------

def tv.keep(b: Bool, at: Nat, w: Nat, rest: List<&2, TChoice.Clash>) -> {TResolve.warns.keep(b, TChoice.Clash{at, w}, rest) == Tw.warns.if(b, at, w, rest) : List<&2, TChoice.Clash>}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

def tv.warns(+ss: List<&2, TResolve.Src>, cs: List<&2, TChoice.Clash>) -> {TResolve.warns(TResolve.seens(ss), cs) == Tw.warns(ss, cs) : List<&2, TChoice.Clash>}:
  match cs:
    case Nil{}:
      {==}
    case c <> +t:
      match c:
        case TChoice.Clash{+at, +w}:
          +xs = TResolve.seens(ss)
          +lhs = TResolve.warns.keep(TResolve.same.at(TResolve.parsed.at(xs, at), TResolve.parsed.at(xs, w)), TChoice.Clash{at, w}, TResolve.warns(xs, t))
          %tv.warns(ss, t) : {lhs == Tw.warns.if(Tw.same(Tw.load.at(ss, at), Tw.load.at(ss, w)), at, w, _) : List<&2, TChoice.Clash>}
          %tv.at(ss, at) : {lhs == Tw.warns.if(Tw.same(_, Tw.load.at(ss, w)), at, w, TResolve.warns(xs, t)) : List<&2, TChoice.Clash>}
          %tv.at(ss, w) : {lhs == Tw.warns.if(Tw.same(TResolve.parsed.at(xs, at), _), at, w, TResolve.warns(xs, t)) : List<&2, TChoice.Clash>}
          %tv.same(TResolve.parsed.at(xs, at), TResolve.parsed.at(xs, w)) : {lhs == Tw.warns.if(_, at, w, TResolve.warns(xs, t)) : List<&2, TChoice.Clash>}
          tv.keep(TResolve.same.at(TResolve.parsed.at(xs, at), TResolve.parsed.at(xs, w)), at, w, TResolve.warns(xs, t))

# The picked file
# ---------------

def tv.picked_if(b: Bool, +ss: List<&2, TResolve.Src>, +id: U32) -> {TResolve.picked.at(TResolve.seens(ss), b, id) == Tw.picked.if(b, ss, id) : Maybe<&2, TPalette.Parsed>}:
  match b:
    case True{}:
      {==}
    case False{}:
      tv.at(ss, U32.to_nat((id - 3 : U32)))

def tv.picked(+ss: List<&2, TResolve.Src>, +id: U32) -> {TResolve.picked(TResolve.seens(ss), id) == Tw.picked(ss, id) : Maybe<&2, TPalette.Parsed>}:
  tv.picked_if(U32.is_lt(id, 3), ss, id)

# One load, spelled
# -----------------

def tv.pick(+ss: List<&2, TResolve.Src>, p: TChoice.Pick) -> {FTh.put_resolved(TResolve.resolve.pick(TResolve.seens(ss), p)) == Tw.answer.pick(ss, p) : String}:
  match p:
    case TChoice.Pick{r, +c, +k, +b}:
      match r:
        case TName.Res{+id, +w}:
          +xs = TResolve.seens(ss)
          +ws = TResolve.warns(xs, k)
          +os = TResolve.outs(xs)
          +pk = TResolve.picked(xs, id)
          +lhs = FTh.put_resolved(TResolve.Resolved{TName.Res{id, w}, c, ws, b, os, pk})
          %tv.picked(ss, id) : {lhs == Wr.put_u32(id, Wr.put_bool(w, Tw.mcause(c, Wr.put_nat(List.length(&2, TChoice.Clash, Tw.warns(ss, k)), Tw.clashes.items(Tw.warns(ss, k), Wr.put_nat(List.length(&2, Nat, b), Tw.nats.items(b, Wr.put_nat(List.length(&2, TResolve.Src, ss), Tw.outs.items(ss, Tw.mparsed(_, "")))))))))) : String}
          %LTWrite.tw.mparsed(pk, "") : {lhs == Wr.put_u32(id, Wr.put_bool(w, Tw.mcause(c, Wr.put_nat(List.length(&2, TChoice.Clash, Tw.warns(ss, k)), Tw.clashes.items(Tw.warns(ss, k), Wr.put_nat(List.length(&2, Nat, b), Tw.nats.items(b, Wr.put_nat(List.length(&2, TResolve.Src, ss), Tw.outs.items(ss, _))))))))) : String}
          %tv.outs(ss, FTh.put_mparsed(pk, "")) : {lhs == Wr.put_u32(id, Wr.put_bool(w, Tw.mcause(c, Wr.put_nat(List.length(&2, TChoice.Clash, Tw.warns(ss, k)), Tw.clashes.items(Tw.warns(ss, k), Wr.put_nat(List.length(&2, Nat, b), Tw.nats.items(b, Wr.put_nat(List.length(&2, TResolve.Src, ss), _)))))))) : String}
          %tv.outs_len(ss) : {lhs == Wr.put_u32(id, Wr.put_bool(w, Tw.mcause(c, Wr.put_nat(List.length(&2, TChoice.Clash, Tw.warns(ss, k)), Tw.clashes.items(Tw.warns(ss, k), Wr.put_nat(List.length(&2, Nat, b), Tw.nats.items(b, Wr.put_nat(_, FTh.put_outs.items(os, FTh.put_mparsed(pk, "")))))))))) : String}
          +tail = Wr.put_nat(List.length(&2, TResolve.Out, os), FTh.put_outs.items(os, FTh.put_mparsed(pk, "")))
          %LTWrite.tw.nats(b, tail) : {lhs == Wr.put_u32(id, Wr.put_bool(w, Tw.mcause(c, Wr.put_nat(List.length(&2, TChoice.Clash, Tw.warns(ss, k)), Tw.clashes.items(Tw.warns(ss, k), Wr.put_nat(List.length(&2, Nat, b), _)))))) : String}
          +tail2 = Wr.put_nat(List.length(&2, Nat, b), FTh.put_nats.items(b, tail))
          %tv.warns(ss, k) : {lhs == Wr.put_u32(id, Wr.put_bool(w, Tw.mcause(c, Wr.put_nat(List.length(&2, TChoice.Clash, _), Tw.clashes.items(_, tail2))))) : String}
          %LTWrite.tw.clashes(ws, tail2) : {lhs == Wr.put_u32(id, Wr.put_bool(w, Tw.mcause(c, Wr.put_nat(List.length(&2, TChoice.Clash, ws), _)))) : String}
          %LTWrite.tw.mcause(c, Wr.put_nat(List.length(&2, TChoice.Clash, ws), FTh.put_clashes.items(ws, tail2))) : {lhs == Wr.put_u32(id, Wr.put_bool(w, _)) : String}
          {==}

# a load: the model's, spelled by the entry, is the laws'
def tv.resolve(+n: String, +ss: List<&2, TResolve.Src>) -> {FTh.put_resolved(TResolve.resolve(n, ss)) == Tw.answer.pick(ss, TChoice.pick(Tw.lds(ss), n)) : String}:
  %tv.lds(ss) : {FTh.put_resolved(TResolve.resolve(n, ss)) == Tw.answer.pick(ss, TChoice.pick(_, n)) : String}
  tv.pick(ss, TChoice.pick(TResolve.lds(TResolve.seens(ss)), n))
