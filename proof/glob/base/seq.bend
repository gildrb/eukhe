# eukhe: lemmas on what alternatives of byte items match, for the proofs
# of glob_match_* and glob_token_*: the matcher's search over alternatives
# is an or of the R4 split (gs.af); the items a ++ b match bytes when a
# matches a prefix and b the rest (gs.cat); so the products of two lists
# of alternatives match the splits (gs.cross). An or over the split
# points 0..i is spelled as a recursion on i (gs.S, gs.SA, gs.SX).

import Base
import ../../../bend/glob/parse.bend as GParse
import ../../../bend/glob/items.bend as GItems
import ../../../bend/glob/match.bend as GMatch
import ../../../laws/glob.bend as Glob
import ./logic.bend as GL
import ./match.bend as GB

# Alternatives
# ------------

# one of the alternatives xs matches bs (R4)
def gs.OL(+bs: List<&2, U32>, xs: List<&2, List<&2, GItems.It>>) -> Bool:
  match xs:
    case Nil{}:
      False{}
    case a <> r:
      Bool.or(Glob.sp_lang(bs, a), gs.OL(bs, r))

def gs.af_or(b: Bool, +r: Bool) -> {GMatch.or_else(b, u => r) == Bool.or(b, r) : Bool}:
  match b:
    case True{}:
      {==}
    case False{}:
      {==}

# the matcher's search over alternatives
def gs.af(+bs: List<&2, U32>, xs: List<&2, List<&2, GItems.It>>) -> {GMatch.any_full(bs, xs) == gs.OL(bs, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +r:
      %Equal.sym(Bool, GMatch.full(bs, a), Glob.sp_lang(bs, a), GB.gb.full(bs, a)) : {GMatch.or_else(_, u => GMatch.any_full(bs, r)) == Bool.or(Glob.sp_lang(bs, a), gs.OL(bs, r)) : Bool}
      %gs.af(bs, r) : {GMatch.or_else(Glob.sp_lang(bs, a), u => GMatch.any_full(bs, r)) == Bool.or(Glob.sp_lang(bs, a), _) : Bool}
      gs.af_or(Glob.sp_lang(bs, a), GMatch.any_full(bs, r))

def gs.ol_app(+bs: List<&2, U32>, xs: List<&2, List<&2, GItems.It>>, +ys: List<&2, List<&2, GItems.It>>) -> {gs.OL(bs, List.append(&2, List<&2, GItems.It>, xs, ys)) == Bool.or(gs.OL(bs, xs), gs.OL(bs, ys)) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +r:
      %Equal.sym(Bool, gs.OL(bs, List.append(&2, List<&2, GItems.It>, r, ys)), Bool.or(gs.OL(bs, r), gs.OL(bs, ys)), gs.ol_app(bs, r, ys)) : {Bool.or(Glob.sp_lang(bs, a), _) == Bool.or(Bool.or(Glob.sp_lang(bs, a), gs.OL(bs, r)), gs.OL(bs, ys)) : Bool}
      Equal.sym(Bool, Bool.or(Bool.or(Glob.sp_lang(bs, a), gs.OL(bs, r)), gs.OL(bs, ys)), Bool.or(Glob.sp_lang(bs, a), Bool.or(gs.OL(bs, r), gs.OL(bs, ys))), GL.gl.or_assoc(Glob.sp_lang(bs, a), gs.OL(bs, r), gs.OL(bs, ys)))

# the empty alternative list appended changes nothing
def gs.ol_nil(+bs: List<&2, U32>, +xs: List<&2, List<&2, GItems.It>>) -> {gs.OL(bs, List.append(&2, List<&2, GItems.It>, xs, Nil{})) == gs.OL(bs, xs) : Bool}:
  Equal.cong(List<&2, List<&2, GItems.It>>, Bool, z => gs.OL(bs, z), List.append(&2, List<&2, GItems.It>, xs, Nil{}), xs, GL.gl.app_nil(List<&2, GItems.It>, xs))

# Splits
# ------

# some split point j <= i: a matches the first j bytes, b the rest
def gs.S(+a: List<&2, GItems.It>, +b: List<&2, GItems.It>, +bs: List<&2, U32>, i: Nat) -> Bool:
  match i:
    case 0n:
      Bool.and(Glob.sp_lang(Nil{}, a), Glob.sp_lang(bs, b))
    case 1n++j:
      Bool.or(Bool.and(Glob.sp_lang(List.take(&2, U32, bs, 1n+j), a), Glob.sp_lang(List.drop(&2, U32, bs, 1n+j), b)), gs.S(a, b, bs, j))

# the empty items take the empty prefix only
def gs.S_nil(+b: List<&2, GItems.It>, +x: U32, +t: List<&2, U32>, k: Nat) -> {gs.S(Nil{}, b, x <> t, k) == Glob.sp_lang(x <> t, b) : Bool}:
  match k:
    case 0n:
      {==}
    case 1n+j:
      gs.S_nil(b, x, t, j)

# the splits after the first byte or none
def gs.S1(+a: List<&2, GItems.It>, +b: List<&2, GItems.It>, +x: U32, t: List<&2, U32>) -> {gs.S(a, b, x <> t, 1n) == Bool.or(Bool.and(Glob.sp_lang([x], a), Glob.sp_lang(t, b)), Bool.and(Glob.sp_lang(Nil{}, a), Glob.sp_lang(x <> t, b))) : Bool}:
  match t:
    case Nil{}:
      {==}
    case y <> u:
      {==}

# a byte item first: it takes the first byte
def gs.S_one(+c: GItems.BC, +a: List<&2, GItems.It>, +b: List<&2, GItems.It>, +x: U32, +t: List<&2, U32>, k: Nat) -> {gs.S(GItems.One{c} <> a, b, x <> t, 1n+k) == Bool.and(GMatch.bc(c, x), gs.S(a, b, t, k)) : Bool}:
  match k:
    case 0n:
      +p = GMatch.bc(c, x)
      +q = Glob.sp_lang(Nil{}, a)
      +r = Glob.sp_lang(t, b)
      %Equal.sym(Bool, gs.S(GItems.One{c} <> a, b, x <> t, 1n), Bool.or(Bool.and(Glob.sp_lang([x], GItems.One{c} <> a), r), Bool.and(Glob.sp_lang(Nil{}, GItems.One{c} <> a), Glob.sp_lang(x <> t, b))), gs.S1(GItems.One{c} <> a, b, x, t)) : {_ == Bool.and(p, Bool.and(q, r)) : Bool}
      %Equal.sym(Bool, Bool.or(Bool.and(Bool.and(p, q), r), False{}), Bool.and(Bool.and(p, q), r), GL.gl.or_false(Bool.and(Bool.and(p, q), r))) : {_ == Bool.and(p, Bool.and(q, r)) : Bool}
      GL.gl.and_assoc(p, q, r)
    case 1n++j:
      +p = GMatch.bc(c, x)
      +q = Glob.sp_lang(List.take(&2, U32, t, 1n+j), a)
      +r = Glob.sp_lang(List.drop(&2, U32, t, 1n+j), b)
      +s = gs.S(a, b, t, j)
      %Equal.sym(Bool, gs.S(GItems.One{c} <> a, b, x <> t, 1n+j), Bool.and(p, s), gs.S_one(c, a, b, x, t, j)) : {Bool.or(Bool.and(Bool.and(p, q), r), _) == Bool.and(p, Bool.or(Bool.and(q, r), s)) : Bool}
      %Equal.sym(Bool, Bool.and(Bool.and(p, q), r), Bool.and(p, Bool.and(q, r)), GL.gl.and_assoc(p, q, r)) : {Bool.or(_, Bool.and(p, s)) == Bool.and(p, Bool.or(Bool.and(q, r), s)) : Bool}
      Equal.sym(Bool, Bool.and(p, Bool.or(Bool.and(q, r), s)), Bool.or(Bool.and(p, Bool.and(q, r)), Bool.and(p, s)), GL.gl.and_or(p, Bool.and(q, r), s))

# (p or q) or t is (p or t) or q
def gs.or_rot(p: Bool, +q: Bool, t: Bool) -> {Bool.or(Bool.or(p, q), t) == Bool.or(Bool.or(p, t), q) : Bool}:
  match p t:
    case True{} t:
      {==}
    case False{} True{}:
      GL.gl.or_true(q)
    case False{} False{}:
      GL.gl.or_false(q)

# a star first: it takes no byte, or the first byte and stays
def gs.S_star(+c: GItems.BC, +a: List<&2, GItems.It>, +b: List<&2, GItems.It>, +x: U32, +t: List<&2, U32>, k: Nat) -> {gs.S(GItems.Star{c} <> a, b, x <> t, 1n+k) == Bool.or(gs.S(a, b, x <> t, 1n+k), Bool.and(GMatch.bc(c, x), gs.S(GItems.Star{c} <> a, b, t, k))) : Bool}:
  match k:
    case 0n:
      +g = GMatch.bc(c, x)
      +la = Glob.sp_lang([x], a)
      +ls = Glob.sp_lang(Nil{}, a)
      +lb = Glob.sp_lang(t, b)
      +t0 = Bool.and(ls, Glob.sp_lang(x <> t, b))
      +s1 = Bool.or(Bool.and(la, lb), t0)
      %Equal.sym(Bool, gs.S(GItems.Star{c} <> a, b, x <> t, 1n), Bool.or(Bool.and(Glob.sp_lang([x], GItems.Star{c} <> a), lb), Bool.and(Glob.sp_lang(Nil{}, GItems.Star{c} <> a), Glob.sp_lang(x <> t, b))), gs.S1(GItems.Star{c} <> a, b, x, t)) : {_ == Bool.or(gs.S(a, b, x <> t, 1n), Bool.and(g, Bool.and(ls, lb))) : Bool}
      %Equal.sym(Bool, gs.S(a, b, x <> t, 1n), s1, gs.S1(a, b, x, t)) : {Bool.or(Bool.and(Bool.or(la, Bool.and(g, ls)), lb), t0) == Bool.or(_, Bool.and(g, Bool.and(ls, lb))) : Bool}
      %Equal.sym(Bool, Bool.and(Bool.or(la, Bool.and(g, ls)), lb), Bool.or(Bool.and(la, lb), Bool.and(Bool.and(g, ls), lb)), GL.gl.or_and(la, Bool.and(g, ls), lb)) : {Bool.or(_, t0) == Bool.or(Bool.or(Bool.and(la, lb), t0), Bool.and(g, Bool.and(ls, lb))) : Bool}
      %Equal.sym(Bool, Bool.and(Bool.and(g, ls), lb), Bool.and(g, Bool.and(ls, lb)), GL.gl.and_assoc(g, ls, lb)) : {Bool.or(Bool.or(Bool.and(la, lb), _), t0) == Bool.or(Bool.or(Bool.and(la, lb), t0), Bool.and(g, Bool.and(ls, lb))) : Bool}
      gs.or_rot(Bool.and(la, lb), Bool.and(g, Bool.and(ls, lb)), t0)
    case 1n++j:
      +g = GMatch.bc(c, x)
      +tk = List.take(&2, U32, t, 1n+j)
      +la = Glob.sp_lang(x <> tk, a)
      +ls = Glob.sp_lang(tk, GItems.Star{c} <> a)
      +lb = Glob.sp_lang(List.drop(&2, U32, t, 1n+j), b)
      +r = gs.S(a, b, x <> t, 1n+j)
      +u = Bool.and(g, gs.S(GItems.Star{c} <> a, b, t, j))
      %Equal.sym(Bool, gs.S(GItems.Star{c} <> a, b, x <> t, 1n+j), Bool.or(r, u), gs.S_star(c, a, b, x, t, j)) : {Bool.or(Bool.and(Bool.or(la, Bool.and(g, ls)), lb), _) == Bool.or(Bool.or(Bool.and(la, lb), r), Bool.and(g, Bool.or(Bool.and(ls, lb), gs.S(GItems.Star{c} <> a, b, t, j)))) : Bool}
      %Equal.sym(Bool, Bool.and(Bool.or(la, Bool.and(g, ls)), lb), Bool.or(Bool.and(la, lb), Bool.and(Bool.and(g, ls), lb)), GL.gl.or_and(la, Bool.and(g, ls), lb)) : {Bool.or(_, Bool.or(r, u)) == Bool.or(Bool.or(Bool.and(la, lb), r), Bool.and(g, Bool.or(Bool.and(ls, lb), gs.S(GItems.Star{c} <> a, b, t, j)))) : Bool}
      %Equal.sym(Bool, Bool.and(g, Bool.or(Bool.and(ls, lb), gs.S(GItems.Star{c} <> a, b, t, j))), Bool.or(Bool.and(g, Bool.and(ls, lb)), u), GL.gl.and_or(g, Bool.and(ls, lb), gs.S(GItems.Star{c} <> a, b, t, j))) : {Bool.or(Bool.or(Bool.and(la, lb), Bool.and(Bool.and(g, ls), lb)), Bool.or(r, u)) == Bool.or(Bool.or(Bool.and(la, lb), r), _) : Bool}
      %Equal.sym(Bool, Bool.and(Bool.and(g, ls), lb), Bool.and(g, Bool.and(ls, lb)), GL.gl.and_assoc(g, ls, lb)) : {Bool.or(Bool.or(Bool.and(la, lb), _), Bool.or(r, u)) == Bool.or(Bool.or(Bool.and(la, lb), r), Bool.or(Bool.and(g, Bool.and(ls, lb)), u)) : Bool}
      GL.gl.or_swap(Bool.and(la, lb), Bool.and(g, Bool.and(ls, lb)), r, u)

# the items a ++ b match bs exactly at some split
def gs.cat(a: List<&2, GItems.It>, +b: List<&2, GItems.It>, bs: List<&2, U32>) -> {Glob.sp_lang(bs, List.append(&2, GItems.It, a, b)) == gs.S(a, b, bs, List.length(&2, U32, bs)) : Bool}:
  match a:
    case Nil{}:
      match bs:
        case Nil{}:
          {==}
        case +x <> +t:
          Equal.sym(Bool, gs.S(Nil{}, b, x <> t, 1n+List.length(&2, U32, t)), Glob.sp_lang(x <> t, b), gs.S_nil(b, x, t, 1n+List.length(&2, U32, t)))
    case i <> +k:
      match i:
        case GItems.One{+c}:
          match bs:
            case Nil{}:
              {==}
            case +x <> +t:
              %Equal.sym(Bool, Glob.sp_lang(t, List.append(&2, GItems.It, k, b)), gs.S(k, b, t, List.length(&2, U32, t)), gs.cat(k, b, t)) : {Bool.and(GMatch.bc(c, x), _) == gs.S(GItems.One{c} <> k, b, x <> t, 1n+List.length(&2, U32, t)) : Bool}
              Equal.sym(Bool, gs.S(GItems.One{c} <> k, b, x <> t, 1n+List.length(&2, U32, t)), Bool.and(GMatch.bc(c, x), gs.S(k, b, t, List.length(&2, U32, t))), gs.S_one(c, k, b, x, t, List.length(&2, U32, t)))
        case GItems.Star{+c}:
          match bs:
            case Nil{}:
              gs.cat(k, b, Nil{})
            case +x <> +t:
              %Equal.sym(Bool, Glob.sp_lang(x <> t, List.append(&2, GItems.It, k, b)), gs.S(k, b, x <> t, 1n+List.length(&2, U32, t)), gs.cat(k, b, x <> t)) : {Bool.or(_, Bool.and(GMatch.bc(c, x), Glob.sp_lang(t, GItems.Star{c} <> List.append(&2, GItems.It, k, b)))) == gs.S(GItems.Star{c} <> k, b, x <> t, 1n+List.length(&2, U32, t)) : Bool}
              %Equal.sym(Bool, Glob.sp_lang(t, List.append(&2, GItems.It, GItems.Star{c} <> k, b)), gs.S(GItems.Star{c} <> k, b, t, List.length(&2, U32, t)), gs.cat(GItems.Star{c} <> k, b, t)) : {Bool.or(gs.S(k, b, x <> t, 1n+List.length(&2, U32, t)), Bool.and(GMatch.bc(c, x), _)) == gs.S(GItems.Star{c} <> k, b, x <> t, 1n+List.length(&2, U32, t)) : Bool}
              Equal.sym(Bool, gs.S(GItems.Star{c} <> k, b, x <> t, 1n+List.length(&2, U32, t)), Bool.or(gs.S(k, b, x <> t, 1n+List.length(&2, U32, t)), Bool.and(GMatch.bc(c, x), gs.S(GItems.Star{c} <> k, b, t, List.length(&2, U32, t)))), gs.S_star(c, k, b, x, t, List.length(&2, U32, t)))

# Products of alternatives
# ------------------------

# some split point j <= i: a matches the first j bytes, an alternative of
# ys the rest
def gs.SA(+a: List<&2, GItems.It>, +ys: List<&2, List<&2, GItems.It>>, +bs: List<&2, U32>, i: Nat) -> Bool:
  match i:
    case 0n:
      Bool.and(Glob.sp_lang(Nil{}, a), gs.OL(bs, ys))
    case 1n++j:
      Bool.or(Bool.and(Glob.sp_lang(List.take(&2, U32, bs, 1n+j), a), gs.OL(List.drop(&2, U32, bs, 1n+j), ys)), gs.SA(a, ys, bs, j))

# some split point j <= i: an alternative of xs matches the first j
# bytes, an alternative of ys the rest
def gs.SX(+xs: List<&2, List<&2, GItems.It>>, +ys: List<&2, List<&2, GItems.It>>, +bs: List<&2, U32>, i: Nat) -> Bool:
  match i:
    case 0n:
      Bool.and(gs.OL(Nil{}, xs), gs.OL(bs, ys))
    case 1n++j:
      Bool.or(Bool.and(gs.OL(List.take(&2, U32, bs, 1n+j), xs), gs.OL(List.drop(&2, U32, bs, 1n+j), ys)), gs.SX(xs, ys, bs, j))

def gs.SA_nil(+a: List<&2, GItems.It>, +bs: List<&2, U32>, i: Nat) -> {gs.SA(a, Nil{}, bs, i) == False{} : Bool}:
  match i:
    case 0n:
      GL.gl.and_false(Glob.sp_lang(Nil{}, a))
    case 1n++j:
      %Equal.sym(Bool, gs.SA(a, Nil{}, bs, j), False{}, gs.SA_nil(a, bs, j)) : {Bool.or(Bool.and(Glob.sp_lang(List.take(&2, U32, bs, 1n+j), a), False{}), _) == False{} : Bool}
      %Equal.sym(Bool, Bool.and(Glob.sp_lang(List.take(&2, U32, bs, 1n+j), a), False{}), False{}, GL.gl.and_false(Glob.sp_lang(List.take(&2, U32, bs, 1n+j), a))) : {Bool.or(_, False{}) == False{} : Bool}
      {==}

def gs.SA_cons(+a: List<&2, GItems.It>, +b: List<&2, GItems.It>, +ys: List<&2, List<&2, GItems.It>>, +bs: List<&2, U32>, i: Nat) -> {gs.SA(a, b <> ys, bs, i) == Bool.or(gs.S(a, b, bs, i), gs.SA(a, ys, bs, i)) : Bool}:
  match i:
    case 0n:
      GL.gl.and_or(Glob.sp_lang(Nil{}, a), Glob.sp_lang(bs, b), gs.OL(bs, ys))
    case 1n++j:
      +la = Glob.sp_lang(List.take(&2, U32, bs, 1n+j), a)
      +lb = Glob.sp_lang(List.drop(&2, U32, bs, 1n+j), b)
      +ly = gs.OL(List.drop(&2, U32, bs, 1n+j), ys)
      %Equal.sym(Bool, gs.SA(a, b <> ys, bs, j), Bool.or(gs.S(a, b, bs, j), gs.SA(a, ys, bs, j)), gs.SA_cons(a, b, ys, bs, j)) : {Bool.or(Bool.and(la, Bool.or(lb, ly)), _) == Bool.or(Bool.or(Bool.and(la, lb), gs.S(a, b, bs, j)), Bool.or(Bool.and(la, ly), gs.SA(a, ys, bs, j))) : Bool}
      %Equal.sym(Bool, Bool.and(la, Bool.or(lb, ly)), Bool.or(Bool.and(la, lb), Bool.and(la, ly)), GL.gl.and_or(la, lb, ly)) : {Bool.or(_, Bool.or(gs.S(a, b, bs, j), gs.SA(a, ys, bs, j))) == Bool.or(Bool.or(Bool.and(la, lb), gs.S(a, b, bs, j)), Bool.or(Bool.and(la, ly), gs.SA(a, ys, bs, j))) : Bool}
      GL.gl.or_swap(Bool.and(la, lb), Bool.and(la, ly), gs.S(a, b, bs, j), gs.SA(a, ys, bs, j))

# the products of a with each alternative of ys match the splits
def gs.pre(+a: List<&2, GItems.It>, ys: List<&2, List<&2, GItems.It>>, +bs: List<&2, U32>) -> {gs.OL(bs, GItems.seq.pre(a, ys)) == gs.SA(a, ys, bs, List.length(&2, U32, bs)) : Bool}:
  match ys:
    case Nil{}:
      Equal.sym(Bool, gs.SA(a, Nil{}, bs, List.length(&2, U32, bs)), False{}, gs.SA_nil(a, bs, List.length(&2, U32, bs)))
    case +b <> +r:
      +n = List.length(&2, U32, bs)
      %Equal.sym(Bool, Glob.sp_lang(bs, List.append(&2, GItems.It, a, b)), gs.S(a, b, bs, n), gs.cat(a, b, bs)) : {Bool.or(_, gs.OL(bs, GItems.seq.pre(a, r))) == gs.SA(a, b <> r, bs, n) : Bool}
      %Equal.sym(Bool, gs.OL(bs, GItems.seq.pre(a, r)), gs.SA(a, r, bs, n), gs.pre(a, r, bs)) : {Bool.or(gs.S(a, b, bs, n), _) == gs.SA(a, b <> r, bs, n) : Bool}
      Equal.sym(Bool, gs.SA(a, b <> r, bs, n), Bool.or(gs.S(a, b, bs, n), gs.SA(a, r, bs, n)), gs.SA_cons(a, b, r, bs, n))

def gs.SX_nil(+ys: List<&2, List<&2, GItems.It>>, +bs: List<&2, U32>, i: Nat) -> {gs.SX(Nil{}, ys, bs, i) == False{} : Bool}:
  match i:
    case 0n:
      {==}
    case 1n+j:
      gs.SX_nil(ys, bs, j)

def gs.SX_cons(+a: List<&2, GItems.It>, +xs: List<&2, List<&2, GItems.It>>, +ys: List<&2, List<&2, GItems.It>>, +bs: List<&2, U32>, i: Nat) -> {gs.SX(a <> xs, ys, bs, i) == Bool.or(gs.SA(a, ys, bs, i), gs.SX(xs, ys, bs, i)) : Bool}:
  match i:
    case 0n:
      GL.gl.or_and(Glob.sp_lang(Nil{}, a), gs.OL(Nil{}, xs), gs.OL(bs, ys))
    case 1n++j:
      +tk = List.take(&2, U32, bs, 1n+j)
      +la = Glob.sp_lang(tk, a)
      +lx = gs.OL(tk, xs)
      +ly = gs.OL(List.drop(&2, U32, bs, 1n+j), ys)
      %Equal.sym(Bool, gs.SX(a <> xs, ys, bs, j), Bool.or(gs.SA(a, ys, bs, j), gs.SX(xs, ys, bs, j)), gs.SX_cons(a, xs, ys, bs, j)) : {Bool.or(Bool.and(Bool.or(la, lx), ly), _) == Bool.or(Bool.or(Bool.and(la, ly), gs.SA(a, ys, bs, j)), Bool.or(Bool.and(lx, ly), gs.SX(xs, ys, bs, j))) : Bool}
      %Equal.sym(Bool, Bool.and(Bool.or(la, lx), ly), Bool.or(Bool.and(la, ly), Bool.and(lx, ly)), GL.gl.or_and(la, lx, ly)) : {Bool.or(_, Bool.or(gs.SA(a, ys, bs, j), gs.SX(xs, ys, bs, j))) == Bool.or(Bool.or(Bool.and(la, ly), gs.SA(a, ys, bs, j)), Bool.or(Bool.and(lx, ly), gs.SX(xs, ys, bs, j))) : Bool}
      GL.gl.or_swap(Bool.and(la, ly), Bool.and(lx, ly), gs.SA(a, ys, bs, j), gs.SX(xs, ys, bs, j))

# the products of two alternative lists match the splits
def gs.cross(xs: List<&2, List<&2, GItems.It>>, +ys: List<&2, List<&2, GItems.It>>, +bs: List<&2, U32>) -> {gs.OL(bs, GItems.seq.cross(xs, ys)) == gs.SX(xs, ys, bs, List.length(&2, U32, bs)) : Bool}:
  match xs:
    case Nil{}:
      Equal.sym(Bool, gs.SX(Nil{}, ys, bs, List.length(&2, U32, bs)), False{}, gs.SX_nil(ys, bs, List.length(&2, U32, bs)))
    case +a <> +r:
      +n = List.length(&2, U32, bs)
      %Equal.sym(Bool, gs.OL(bs, List.append(&2, List<&2, GItems.It>, GItems.seq.pre(a, ys), GItems.seq.cross(r, ys))), Bool.or(gs.OL(bs, GItems.seq.pre(a, ys)), gs.OL(bs, GItems.seq.cross(r, ys))), gs.ol_app(bs, GItems.seq.pre(a, ys), GItems.seq.cross(r, ys))) : {_ == gs.SX(a <> r, ys, bs, n) : Bool}
      %Equal.sym(Bool, gs.OL(bs, GItems.seq.pre(a, ys)), gs.SA(a, ys, bs, n), gs.pre(a, ys, bs)) : {Bool.or(_, gs.OL(bs, GItems.seq.cross(r, ys))) == gs.SX(a <> r, ys, bs, n) : Bool}
      %Equal.sym(Bool, gs.OL(bs, GItems.seq.cross(r, ys)), gs.SX(r, ys, bs, n), gs.cross(r, ys, bs)) : {Bool.or(gs.SA(a, ys, bs, n), _) == gs.SX(a <> r, ys, bs, n) : Bool}
      Equal.sym(Bool, gs.SX(a <> r, ys, bs, n), Bool.or(gs.SA(a, ys, bs, n), gs.SX(r, ys, bs, n)), gs.SX_cons(a, r, ys, bs, n))

# the products with the one empty alternative are the alternatives
def gs.cross_unit(xs: List<&2, List<&2, GItems.It>>, +bs: List<&2, U32>) -> {gs.OL(bs, GItems.seq.cross(xs, [Nil{}])) == gs.OL(bs, xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case +a <> +r:
      %Equal.sym(Bool, gs.OL(bs, GItems.seq.cross(r, [Nil{}])), gs.OL(bs, r), gs.cross_unit(r, bs)) : {Bool.or(Glob.sp_lang(bs, List.append(&2, GItems.It, a, Nil{})), _) == Bool.or(Glob.sp_lang(bs, a), gs.OL(bs, r)) : Bool}
      %Equal.sym(List<&2, GItems.It>, List.append(&2, GItems.It, a, Nil{}), a, GL.gl.app_nil(GItems.It, a)) : {Bool.or(Glob.sp_lang(bs, _), gs.OL(bs, r)) == Bool.or(Glob.sp_lang(bs, a), gs.OL(bs, r)) : Bool}
      {==}

# Patterns
# --------

# one branch matches as the alternatives of its tokens do
def gs.m(+o: GItems.Opts, +ts: List<&2, GParse.Tok>, +bs: List<&2, U32>) -> {Glob.sp_m(o, ts, bs) == gs.OL(bs, GItems.seq(o, ts)) : Bool}:
  %Equal.sym(Bool, GMatch.any_full(bs, List.append(&2, List<&2, GItems.It>, GItems.seq(o, ts), Nil{})), gs.OL(bs, List.append(&2, List<&2, GItems.It>, GItems.seq(o, ts), Nil{})), gs.af(bs, List.append(&2, List<&2, GItems.It>, GItems.seq(o, ts), Nil{}))) : {_ == gs.OL(bs, GItems.seq(o, ts)) : Bool}
  gs.ol_nil(bs, GItems.seq(o, ts))

# one token alone matches as its alternatives do
def gs.m1(+o: GItems.Opts, +t: GParse.Tok, +bs: List<&2, U32>) -> {Glob.sp_m(o, [t], bs) == gs.OL(bs, GItems.tok(o, t)) : Bool}:
  %Equal.sym(Bool, Glob.sp_m(o, [t], bs), gs.OL(bs, GItems.seq(o, [t])), gs.m(o, [t], bs)) : {_ == gs.OL(bs, GItems.tok(o, t)) : Bool}
  gs.cross_unit(GItems.tok(o, t), bs)
