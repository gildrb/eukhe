# eukhe: the proof of LAW glob_parse_plain
#
# PROOF: a char that is none of `*?[{},\` is of kind KLit (pl.kind, one
# test at a time, each special char refuted by the premise), so a step
# pushes it as a literal and keeps the parser in its normal mode with no
# error (pl.step0 for the first char, pl.step after); over the whole text
# (pl.go) the branch holds the literals last first (pl.acc), which the end
# reverses into the text's order (pl.rev).

import Base
import ../../bend/glob.bend as G
import ../../bend/ffi_glob.bend as FG
import ../../bend/wire.bend as Wr
import ../../laws/base.bend as LawsBase
import ../../laws/glob.bend as Glob
import ../base/logic/bool.bend as LLogicBool
import ../base/staging.bend as LStg

def pl.acc(t: String, a: List<&2, G.Tok>) -> List<&2, G.Tok>:
  match t:
    case SNil{}:
      a
    case SCon{c, u}:
      pl.acc(u, G.TLit{c} <> a)

def pl.last(t: String, p: Maybe<&2, Char>) -> Maybe<&2, Char>:
  match t:
    case SNil{}:
      p
    case SCon{c, u}:
      pl.last(u, Some{c})

def pl.k7(b: Bool, h: {Bool.not(b) == True{} : Bool}) -> {G.kind.g(b) == G.KLit{} : G.K}:
  match b:
    case True{}:
      LStg.stg.absurdF({G.kind.g(True{}) == G.KLit{} : G.K}, h)
    case False{}:
      {==}

def pl.k6(+x: U32, b: Bool, h: {Bool.not(Bool.or(b, U32.is_eq(x, 92))) == True{} : Bool}) -> {G.kind.f(x, b) == G.KLit{} : G.K}:
  match b:
    case True{}:
      LStg.stg.absurdF({G.kind.f(x, True{}) == G.KLit{} : G.K}, h)
    case False{}:
      pl.k7(U32.is_eq(x, 92), h)

def pl.k5(+x: U32, b: Bool, h: {Bool.not(Bool.or(b, Bool.or(U32.is_eq(x, 44), U32.is_eq(x, 92)))) == True{} : Bool}) -> {G.kind.e(x, b) == G.KLit{} : G.K}:
  match b:
    case True{}:
      LStg.stg.absurdF({G.kind.e(x, True{}) == G.KLit{} : G.K}, h)
    case False{}:
      pl.k6(x, U32.is_eq(x, 44), h)

def pl.k4(+x: U32, b: Bool, h: {Bool.not(Bool.or(b, Bool.or(U32.is_eq(x, 125), Bool.or(U32.is_eq(x, 44), U32.is_eq(x, 92))))) == True{} : Bool}) -> {G.kind.d(x, b) == G.KLit{} : G.K}:
  match b:
    case True{}:
      LStg.stg.absurdF({G.kind.d(x, True{}) == G.KLit{} : G.K}, h)
    case False{}:
      pl.k5(x, U32.is_eq(x, 125), h)

def pl.k3(+x: U32, b: Bool, h: {Bool.not(Bool.or(b, Bool.or(U32.is_eq(x, 123), Bool.or(U32.is_eq(x, 125), Bool.or(U32.is_eq(x, 44), U32.is_eq(x, 92)))))) == True{} : Bool}) -> {G.kind.c(x, b) == G.KLit{} : G.K}:
  match b:
    case True{}:
      LStg.stg.absurdF({G.kind.c(x, True{}) == G.KLit{} : G.K}, h)
    case False{}:
      pl.k4(x, U32.is_eq(x, 123), h)

def pl.k2(+x: U32, b: Bool, h: {Bool.not(Bool.or(b, Bool.or(U32.is_eq(x, 91), Bool.or(U32.is_eq(x, 123), Bool.or(U32.is_eq(x, 125), Bool.or(U32.is_eq(x, 44), U32.is_eq(x, 92))))))) == True{} : Bool}) -> {G.kind.b(x, b) == G.KLit{} : G.K}:
  match b:
    case True{}:
      LStg.stg.absurdF({G.kind.b(x, True{}) == G.KLit{} : G.K}, h)
    case False{}:
      pl.k3(x, U32.is_eq(x, 91), h)

def pl.k1(+x: U32, b: Bool, h: {Bool.not(Bool.or(b, Bool.or(U32.is_eq(x, 63), Bool.or(U32.is_eq(x, 91), Bool.or(U32.is_eq(x, 123), Bool.or(U32.is_eq(x, 125), Bool.or(U32.is_eq(x, 44), U32.is_eq(x, 92)))))))) == True{} : Bool}) -> {G.kind.a(x, b) == G.KLit{} : G.K}:
  match b:
    case True{}:
      LStg.stg.absurdF({G.kind.a(x, True{}) == G.KLit{} : G.K}, h)
    case False{}:
      pl.k2(x, U32.is_eq(x, 63), h)

# a char none of `*?[{},\` is a literal
def pl.kind(+x: U32, h: {Bool.not(Bool.or(U32.is_eq(x, 42), Bool.or(U32.is_eq(x, 63), Bool.or(U32.is_eq(x, 91), Bool.or(U32.is_eq(x, 123), Bool.or(U32.is_eq(x, 125), Bool.or(U32.is_eq(x, 44), U32.is_eq(x, 92)))))))) == True{} : Bool}) -> {G.kind(x) == G.KLit{} : G.K}:
  pl.k1(x, U32.is_eq(x, 42), h)

def pl.step0(c: Char, k: {G.kind(G.code(c)) == G.KLit{} : G.K}) -> {G.step(G.St{G.br0(), Nil{}, None{}, G.MNorm{}, None{}}, c) == G.St{G.Br{[[G.TLit{c}]], True{}, False{}, False{}}, Nil{}, Some{c}, G.MNorm{}, None{}} : G.St}:
  match c:
    case Chr{+x}:
      %Equal.sym(G.K, G.kind(x), G.KLit{}, k) : {G.step.set_prev(G.norm.k(G.St{G.br0(), Nil{}, None{}, G.MNorm{}, None{}}, Chr{x}, _), Chr{x}) == G.St{G.Br{[[G.TLit{Chr{x}}]], True{}, False{}, False{}}, Nil{}, Some{Chr{x}}, G.MNorm{}, None{}} : G.St}
      {==}

def pl.step(c: Char, a: List<&2, G.Tok>, p: Maybe<&2, Char>, k: {G.kind(G.code(c)) == G.KLit{} : G.K}) -> {G.step(G.St{G.Br{[a], True{}, False{}, False{}}, Nil{}, p, G.MNorm{}, None{}}, c) == G.St{G.Br{[G.TLit{c} <> a], True{}, False{}, False{}}, Nil{}, Some{c}, G.MNorm{}, None{}} : G.St}:
  match c:
    case Chr{+x}:
      %Equal.sym(G.K, G.kind(x), G.KLit{}, k) : {G.step.set_prev(G.norm.k(G.St{G.Br{[a], True{}, False{}, False{}}, Nil{}, p, G.MNorm{}, None{}}, Chr{x}, _), Chr{x}) == G.St{G.Br{[G.TLit{Chr{x}} <> a], True{}, False{}, False{}}, Nil{}, Some{Chr{x}}, G.MNorm{}, None{}} : G.St}
      {==}

# the head char of a plain text is a literal
def pl.hk(c: Char, +u: String, h: {Glob.sp_plain(SCon{c, u}) == True{} : Bool}) -> {G.kind(G.code(c)) == G.KLit{} : G.K}:
  match c:
    case Chr{+x}:
      pl.kind(x, LLogicBool.tree.pt.and_l(Bool.not(Bool.or(U32.is_eq(x, 42), Bool.or(U32.is_eq(x, 63), Bool.or(U32.is_eq(x, 91), Bool.or(U32.is_eq(x, 123), Bool.or(U32.is_eq(x, 125), Bool.or(U32.is_eq(x, 44), U32.is_eq(x, 92)))))))), Glob.sp_plain(u), h))

# the rest of a plain text is plain
def pl.hr(c: Char, +u: String, h: {Glob.sp_plain(SCon{c, u}) == True{} : Bool}) -> {Glob.sp_plain(u) == True{} : Bool}:
  match c:
    case Chr{+x}:
      LLogicBool.tree.pt.and_r(Bool.not(Bool.or(U32.is_eq(x, 42), Bool.or(U32.is_eq(x, 63), Bool.or(U32.is_eq(x, 91), Bool.or(U32.is_eq(x, 123), Bool.or(U32.is_eq(x, 125), Bool.or(U32.is_eq(x, 44), U32.is_eq(x, 92)))))))), Glob.sp_plain(u), h)

# a plain text pushes its literals, last first
def pl.go(t: String, +a: List<&2, G.Tok>, +p: Maybe<&2, Char>, h: {Glob.sp_plain(t) == True{} : Bool}) -> {G.go(t, G.St{G.Br{[a], True{}, False{}, False{}}, Nil{}, p, G.MNorm{}, None{}}) == G.St{G.Br{[pl.acc(t, a)], True{}, False{}, False{}}, Nil{}, pl.last(t, p), G.MNorm{}, None{}} : G.St}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      +h1 = h
      +k = pl.hk(c, u, h1)
      +hu = pl.hr(c, u, h1)
      %Equal.sym(G.St, G.step(G.St{G.Br{[a], True{}, False{}, False{}}, Nil{}, p, G.MNorm{}, None{}}, c), G.St{G.Br{[G.TLit{c} <> a], True{}, False{}, False{}}, Nil{}, Some{c}, G.MNorm{}, None{}}, pl.step(c, a, p, k)) : {G.go(u, _) == G.St{G.Br{[pl.acc(SCon{c, u}, a)], True{}, False{}, False{}}, Nil{}, pl.last(SCon{c, u}, p), G.MNorm{}, None{}} : G.St}
      pl.go(u, G.TLit{c} <> a, Some{c}, hu)

# the literals, reversed, are the text's
def pl.rev(t: String, a: List<&2, G.Tok>) -> {List.reverse.go(&2, G.Tok, pl.acc(t, a), Nil{}) == List.reverse.go(&2, G.Tok, a, Glob.sp_lits(t)) : List<&2, G.Tok>}:
  match t:
    case SNil{}:
      {==}
    case SCon{+c, u}:
      pl.rev(u, G.TLit{c} <> a)

def Glob.glob_parse_plain(s, h):
  match s:
    case SNil{}:
      {==}
    case SCon{+c, +u}:
      +h1 = h
      +k = pl.hk(c, u, h1)
      +hu = pl.hr(c, u, h1)
      %Equal.sym(G.St, G.step(G.St{G.br0(), Nil{}, None{}, G.MNorm{}, None{}}, c), G.St{G.Br{[[G.TLit{c}]], True{}, False{}, False{}}, Nil{}, Some{c}, G.MNorm{}, None{}}, pl.step0(c, k)) : {G.fin(G.go(u, _)) == Done{G.Glob{[Glob.sp_lits(SCon{c, u})], False{}}} : Result<&2, &2, G.Err, G.Glob>}
      %Equal.sym(G.St, G.go(u, G.St{G.Br{[[G.TLit{c}]], True{}, False{}, False{}}, Nil{}, Some{c}, G.MNorm{}, None{}}), G.St{G.Br{[pl.acc(u, [G.TLit{c}])], True{}, False{}, False{}}, Nil{}, pl.last(u, Some{c}), G.MNorm{}, None{}}, pl.go(u, [G.TLit{c}], Some{c}, hu)) : {G.fin(_) == Done{G.Glob{[Glob.sp_lits(SCon{c, u})], False{}}} : Result<&2, &2, G.Err, G.Glob>}
      %Equal.sym(List<&2, G.Tok>, List.reverse.go(&2, G.Tok, pl.acc(u, [G.TLit{c}]), Nil{}), List.reverse.go(&2, G.Tok, [G.TLit{c}], Glob.sp_lits(u)), pl.rev(u, [G.TLit{c}])) : {Done{G.Glob{[_], False{}}} == Done{G.Glob{[Glob.sp_lits(SCon{c, u})], False{}}} : Result<&2, &2, G.Err, G.Glob>}
      {==}
