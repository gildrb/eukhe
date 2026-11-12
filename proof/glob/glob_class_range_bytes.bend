# eukhe: the proof of LAW glob_class_range_bytes
#
# PROOF: per char range: one char gives its bytes (singles is sp_ones
# before the rest); else the code splits lo's bytes into all but the last
# and the last (split_last is take and sp_last) and joins the last to hi's
# first byte, hi's other bytes after (UTF-8 forms are never empty).

import Base
import ../../bend/glob/parse.bend as GParse
import ../../bend/glob/items.bend as GItems
import ../../laws/glob.bend as Glob
import ./base/logic.bend as GL

def rb.singles(bs: List<&2, U32>, -rest: List<&2, GItems.BR>) -> {GItems.singles(bs, rest) == List.append(&2, GItems.BR, Glob.sp_ones(bs), rest) : List<&2, GItems.BR>}:
  match bs:
    case Nil{}:
      {==}
    case +b <> t:
      Equal.cong(List<&2, GItems.BR>, List<&2, GItems.BR>, z => GItems.BR{b, b} <> z, GItems.singles(t, rest), List.append(&2, GItems.BR, Glob.sp_ones(t), rest), rb.singles(t, rest))

def rb.split(r: List<&2, U32>, +b: U32) -> {GItems.split_last(r, b) == (List.take(&2, U32, b <> r, List.length(&2, U32, r)), Glob.sp_last(r, b)) : List<&2, U32> & U32}:
  match r:
    case Nil{}:
      {==}
    case +c <> +t:
      %Equal.sym(List<&2, U32> & U32, GItems.split_last(t, c), (List.take(&2, U32, c <> t, List.length(&2, U32, t)), Glob.sp_last(t, c)), rb.split(t, c)) : {GItems.split_last.cons(b, _) == (b <> List.take(&2, U32, c <> t, List.length(&2, U32, t)), Glob.sp_last(t, c)) : List<&2, U32> & U32}
      {==}

def rb.sub0(n: Nat) -> {Nat.sub(n, 0n) == n : Nat}:
  match n:
    case 0n:
      {==}
    case 1n+m:
      {==}

def rb.drop0(t: List<&2, U32>) -> {List.drop(&2, U32, t, 0n) == t : List<&2, U32>}:
  match t:
    case Nil{}:
      {==}
    case x <> u:
      {==}

# a UTF-8 form is a first byte and the others
def rb.Ex(bs: List<&2, U32>) -> Type:
  &h: U32 -> &t: List<&2, U32> -> {bs == h <> t : List<&2, U32>}

def rb.exd(+x: U32, c: Bool) -> rb.Ex(GItems.utf8.d(x, Nil{}, c)):
  match c:
    case True{}:
      (U32.or(224, U32.shrn(x, 12n)), ([U32.or(128, U32.and(U32.shrn(x, 6n), 63)), U32.or(128, U32.and(x, 63))], {==}))
    case False{}:
      (U32.or(240, U32.shrn(x, 18n)), ([U32.or(128, U32.and(U32.shrn(x, 12n), 63)), U32.or(128, U32.and(U32.shrn(x, 6n), 63)), U32.or(128, U32.and(x, 63))], {==}))

def rb.exc(+x: U32, b: Bool) -> rb.Ex(GItems.utf8.c(x, Nil{}, b)):
  match b:
    case True{}:
      (U32.or(192, U32.shrn(x, 6n)), ([U32.or(128, U32.and(x, 63))], {==}))
    case False{}:
      rb.exd(x, U32.is_lt(x, 65536))

def rb.exb(+x: U32, a: Bool) -> rb.Ex(GItems.utf8.b(x, Nil{}, a)):
  match a:
    case True{}:
      (x, (Nil{}, {==}))
    case False{}:
      rb.exc(x, U32.is_lt(x, 2048))

def rb.ex(+x: U32) -> rb.Ex(GItems.utf8(x, Nil{})):
  rb.exb(x, U32.is_lt(x, 128))

# two different chars, of the bytes b <> r and h0 <> ht
def rb.mid(+b: U32, +r: List<&2, U32>, +h0: U32, +ht: List<&2, U32>, +rest: List<&2, GItems.BR>) -> {GItems.rg.mid(GItems.split_last(r, b), h0 <> ht, rest) == List.append(&2, GItems.BR, Glob.sp_rg(False{}, b <> r, h0 <> ht), rest) : List<&2, GItems.BR>}:
  +tk = List.take(&2, U32, b <> r, List.length(&2, U32, r))
  +br = {GItems.BR{Glob.sp_last(r, b), h0} : GItems.BR}
  %Equal.sym(List<&2, U32> & U32, GItems.split_last(r, b), (tk, Glob.sp_last(r, b)), rb.split(r, b)) : {GItems.rg.mid(_, h0 <> ht, rest) == List.append(&2, GItems.BR, Glob.sp_rg(False{}, b <> r, h0 <> ht), rest) : List<&2, GItems.BR>}
  %Equal.sym(Nat, Nat.sub(List.length(&2, U32, r), 0n), List.length(&2, U32, r), rb.sub0(List.length(&2, U32, r))) : {GItems.singles(tk, br <> GItems.singles(ht, rest)) == List.append(&2, GItems.BR, List.append(&2, GItems.BR, Glob.sp_ones(List.take(&2, U32, b <> r, _)), br <> Glob.sp_ones(List.drop(&2, U32, ht, 0n))), rest) : List<&2, GItems.BR>}
  %Equal.sym(List<&2, U32>, List.drop(&2, U32, ht, 0n), ht, rb.drop0(ht)) : {GItems.singles(tk, br <> GItems.singles(ht, rest)) == List.append(&2, GItems.BR, List.append(&2, GItems.BR, Glob.sp_ones(tk), br <> Glob.sp_ones(_)), rest) : List<&2, GItems.BR>}
  %Equal.sym(List<&2, GItems.BR>, GItems.singles(tk, br <> GItems.singles(ht, rest)), List.append(&2, GItems.BR, Glob.sp_ones(tk), br <> GItems.singles(ht, rest)), rb.singles(tk, br <> GItems.singles(ht, rest))) : {_ == List.append(&2, GItems.BR, List.append(&2, GItems.BR, Glob.sp_ones(tk), br <> Glob.sp_ones(ht)), rest) : List<&2, GItems.BR>}
  %Equal.sym(List<&2, GItems.BR>, GItems.singles(ht, rest), List.append(&2, GItems.BR, Glob.sp_ones(ht), rest), rb.singles(ht, rest)) : {List.append(&2, GItems.BR, Glob.sp_ones(tk), br <> _) == List.append(&2, GItems.BR, List.append(&2, GItems.BR, Glob.sp_ones(tk), br <> Glob.sp_ones(ht)), rest) : List<&2, GItems.BR>}
  Equal.sym(List<&2, GItems.BR>, List.append(&2, GItems.BR, List.append(&2, GItems.BR, Glob.sp_ones(tk), br <> Glob.sp_ones(ht)), rest), List.append(&2, GItems.BR, Glob.sp_ones(tk), List.append(&2, GItems.BR, br <> Glob.sp_ones(ht), rest)), GL.gl.app_assoc(GItems.BR, Glob.sp_ones(tk), br <> Glob.sp_ones(ht), rest))

def rb.multi(+l: U32, +h: U32, +rest: List<&2, GItems.BR>, el: rb.Ex(GItems.utf8(l, Nil{})), eh: rb.Ex(GItems.utf8(h, Nil{}))) -> {GItems.rg.multi(GItems.utf8(l, Nil{}), h, rest) == List.append(&2, GItems.BR, Glob.sp_rg(False{}, GItems.utf8(l, Nil{}), GItems.utf8(h, Nil{})), rest) : List<&2, GItems.BR>}:
  (b, el1) = el
  (r, pl) = el1
  (h0, eh1) = eh
  (ht, ph) = eh1
  %Equal.sym(List<&2, U32>, GItems.utf8(l, Nil{}), b <> r, pl) : {GItems.rg.multi(_, h, rest) == List.append(&2, GItems.BR, Glob.sp_rg(False{}, _, GItems.utf8(h, Nil{})), rest) : List<&2, GItems.BR>}
  %Equal.sym(List<&2, U32>, GItems.utf8(h, Nil{}), h0 <> ht, ph) : {GItems.rg.mid(GItems.split_last(r, b), _, rest) == List.append(&2, GItems.BR, Glob.sp_rg(False{}, b <> r, _), rest) : List<&2, GItems.BR>}
  rb.mid(b, r, h0, ht, rest)

def rb.k(+l: U32, +h: U32, +rest: List<&2, GItems.BR>, same: Bool) -> {GItems.rg.k(l, h, rest, same) == List.append(&2, GItems.BR, Glob.sp_rg(same, GItems.utf8(l, Nil{}), GItems.utf8(h, Nil{})), rest) : List<&2, GItems.BR>}:
  match same:
    case True{}:
      rb.singles(GItems.utf8(l, Nil{}), rest)
    case False{}:
      rb.multi(l, h, rest, rb.ex(l), rb.ex(h))

def rb.go(rs: List<&2, GParse.Rg>) -> {GItems.rgs(rs) == Glob.sp_rgs(rs) : List<&2, GItems.BR>}:
  match rs:
    case Nil{}:
      {==}
    case r <> +t:
      match r:
        case GParse.Rg{lo, hi}:
          match lo hi:
            case Chr{+x} Chr{+y}:
              +sr = Glob.sp_rg(U32.is_eq(x, y), GItems.utf8(x, Nil{}), GItems.utf8(y, Nil{}))
              Equal.trans(List<&2, GItems.BR>, GItems.rg.k(x, y, GItems.rgs(t), U32.is_eq(x, y)), List.append(&2, GItems.BR, sr, GItems.rgs(t)), List.append(&2, GItems.BR, sr, Glob.sp_rgs(t)), rb.k(x, y, GItems.rgs(t), U32.is_eq(x, y)), Equal.cong(List<&2, GItems.BR>, List<&2, GItems.BR>, z => List.append(&2, GItems.BR, sr, z), GItems.rgs(t), Glob.sp_rgs(t), rb.go(t)))

def Glob.glob_class_range_bytes(rs):
  rb.go(rs)
