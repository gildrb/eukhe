# eukhe: the proof of LAW bound_trim_keeps_later_windows: the tail window of a text, read from its end, takes whole lines from the end while they fit in the cap's bytes and lines; what Rust keeps is the end of the stored text (its last lines, then a piece of the line before), so the window of what it keeps then any later output reads the same lines as the window of the whole stored text then that output: either the stored text is kept whole, or what is kept holds more than the cap's bytes (the window stops on a line at or before the piece, which fits on neither side), or what is kept holds at least as many whole last lines as the cap (the window stops before the piece)

import Base
import ../../bend/bound.bend as Bd
import ../../bend/ffi_bound.bend as FBd
import ../../bend/wire.bend as Wr
import ../../laws/bound.bend as Bound
import ./base.bend as LBound

# Logic
# -----

def tk.If(b: Bool, G: Type) -> Type:
  match b:
    case True{}:
      G
    case False{}:
      Unit

def tk.mk(b: Bool, -G: Type, g: G) -> tk.If(b, G):
  match b:
    case True{}:
      g
    case False{}:
      Unit{}

def tk.use(b: Bool, -G: Type, h: {b == True{} : Bool}, x: tk.If(b, G)) -> G:
  match b:
    case True{}:
      x
    case False{}:
      LBound.bnd.ft(G, h)

# Nats
# ----

def tk.le_add(a: Nat, +t: Nat) -> {Nat.is_le(a, Nat.add(a, t)) == True{} : Bool}:
  match a:
    case 0n:
      LBound.bnd.le0(t)
    case 1n++p:
      tk.le_add(p, t)

def tk.add_sub_l(a: Nat, +t: Nat) -> {Nat.sub(Nat.add(a, t), a) == t : Nat}:
  match a:
    case 0n:
      LBound.bnd.sub_zero(t)
    case 1n++p:
      tk.add_sub_l(p, t)

def tk.sub_succ_add(r: Nat, +u: Nat) -> {Nat.sub(1n+Nat.add(r, u), r) == 1n+u : Nat}:
  match r:
    case 0n:
      {==}
    case 1n++p:
      tk.sub_succ_add(p, u)

def tk.pos_add(r: Nat, +u: Nat) -> {Nat.is_lt(0n, Nat.add(r, 1n+u)) == True{} : Bool}:
  match r:
    case 0n:
      {==}
    case 1n++p:
      {==}

def tk.pos_add2(+r: Nat, v: Nat, h: {Nat.is_lt(0n, v) == True{} : Bool}) -> {Nat.is_lt(0n, Nat.add(r, v)) == True{} : Bool}:
  match v:
    case 0n:
      LBound.bnd.ft({Nat.is_lt(0n, Nat.add(r, 0n)) == True{} : Bool}, h)
    case 1n++u:
      tk.pos_add(r, u)

def tk.lt_nle(c: Nat, s: Nat, h: {Nat.is_lt(c, s) == True{} : Bool}) -> {Nat.is_le(s, c) == False{} : Bool}:
  match c s:
    case 0n 0n:
      LBound.bnd.ft({Nat.is_le(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+t:
      {==}
    case 1n+d 0n:
      LBound.bnd.ft({Nat.is_le(0n, 1n+d) == False{} : Bool}, h)
    case 1n+d 1n+t:
      tk.lt_nle(d, t, h)

def tk.nle_lt(a: Nat, b: Nat, e: {Nat.is_le(a, b) == False{} : Bool}) -> {Nat.is_lt(b, a) == True{} : Bool}:
  match a b:
    case 0n 0n:
      LBound.bnd.tf({Nat.is_lt(0n, 0n) == True{} : Bool}, e)
    case 0n 1n+y:
      LBound.bnd.tf({Nat.is_lt(1n+y, 0n) == True{} : Bool}, e)
    case 1n+x 0n:
      {==}
    case 1n+x 1n+y:
      tk.nle_lt(x, y, e)

def tk.lt_le(a: Nat, b: Nat, c: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_le(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n c:
      LBound.bnd.ft({Nat.is_lt(0n, c) == True{} : Bool}, h1)
    case 0n 1n+y 0n:
      LBound.bnd.ft({Nat.is_lt(0n, 0n) == True{} : Bool}, h2)
    case 0n 1n+y 1n+z:
      {==}
    case 1n+x 0n c:
      LBound.bnd.ft({Nat.is_lt(1n+x, c) == True{} : Bool}, h1)
    case 1n+x 1n+y 0n:
      LBound.bnd.ft({Nat.is_lt(1n+x, 0n) == True{} : Bool}, h2)
    case 1n+x 1n+y 1n+z:
      tk.lt_le(x, y, z, h1, h2)

def tk.le_lt(a: Nat, b: Nat, c: Nat, h1: {Nat.is_le(a, b) == True{} : Bool}, h2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  match a b c:
    case 0n 0n 0n:
      LBound.bnd.ft({Nat.is_lt(0n, 0n) == True{} : Bool}, h2)
    case 0n 0n 1n+z:
      {==}
    case 0n 1n+y 0n:
      LBound.bnd.ft({Nat.is_lt(0n, 0n) == True{} : Bool}, h2)
    case 0n 1n+y 1n+z:
      {==}
    case 1n+x 0n c:
      LBound.bnd.ft({Nat.is_lt(1n+x, c) == True{} : Bool}, h1)
    case 1n+x 1n+y 0n:
      LBound.bnd.ft({Nat.is_lt(1n+x, 0n) == True{} : Bool}, h2)
    case 1n+x 1n+y 1n+z:
      tk.le_lt(x, y, z, h1, h2)

def tk.lt_imp_le(b: Nat, c: Nat, h: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_le(b, c) == True{} : Bool}:
  match b c:
    case 0n c:
      LBound.bnd.le0(c)
    case 1n+y 0n:
      LBound.bnd.ft({Nat.is_le(1n+y, 0n) == True{} : Bool}, h)
    case 1n+y 1n+z:
      tk.lt_imp_le(y, z, h)

def tk.lt_trans(+a: Nat, +b: Nat, +c: Nat, h1: {Nat.is_lt(a, b) == True{} : Bool}, h2: {Nat.is_lt(b, c) == True{} : Bool}) -> {Nat.is_lt(a, c) == True{} : Bool}:
  tk.lt_le(a, b, c, h1, tk.lt_imp_le(b, c, h2))

# r <= c < s gives c - r < s - r
def tk.lt_sub(r: Nat, c: Nat, s: Nat, hrc: {Nat.is_le(r, c) == True{} : Bool}, hcs: {Nat.is_lt(c, s) == True{} : Bool}) -> {Nat.is_lt(Nat.sub(c, r), Nat.sub(s, r)) == True{} : Bool}:
  match r c s:
    case 0n c s:
      %Equal.sym(Nat, Nat.sub(c, 0n), c, LBound.bnd.sub_zero(c)) : {Nat.is_lt(_, Nat.sub(s, 0n)) == True{} : Bool}
      %Equal.sym(Nat, Nat.sub(s, 0n), s, LBound.bnd.sub_zero(s)) : {Nat.is_lt(c, _) == True{} : Bool}
      hcs
    case 1n+x 0n s:
      LBound.bnd.ft({Nat.is_lt(Nat.sub(0n, 1n+x), Nat.sub(s, 1n+x)) == True{} : Bool}, hrc)
    case 1n+x 1n+y 0n:
      LBound.bnd.ft({Nat.is_lt(Nat.sub(1n+y, 1n+x), Nat.sub(0n, 1n+x)) == True{} : Bool}, hcs)
    case 1n+x 1n+y 1n+z:
      tk.lt_sub(x, y, z, hrc, hcs)

def tk.sub_cancel(p: Nat, +S: Nat, +r: Nat) -> {Nat.sub(Nat.add(p, S), Nat.add(p, r)) == Nat.sub(S, r) : Nat}:
  match p:
    case 0n:
      {==}
    case 1n++q:
      tk.sub_cancel(q, S, r)

def tk.le_addl(p: Nat, +S: Nat) -> {Nat.is_le(S, Nat.add(p, S)) == True{} : Bool}:
  match p:
    case 0n:
      LBound.bnd.le_refl(S)
    case 1n++q:
      LBound.bnd.le_trans(S, Nat.add(q, S), 1n+Nat.add(q, S), tk.le_addl(q, S), LBound.bnd.le_succ(Nat.add(q, S)))

def tk.add_lt_mono(p: Nat, +a: Nat, +b: Nat, h: {Nat.is_lt(a, b) == True{} : Bool}) -> {Nat.is_lt(Nat.add(p, a), Nat.add(p, b)) == True{} : Bool}:
  match p:
    case 0n:
      h
    case 1n++q:
      tk.add_lt_mono(q, a, b, h)

def tk.sub_le0(a: Nat, b: Nat, h: {Nat.is_le(a, b) == True{} : Bool}) -> {Nat.sub(a, b) == 0n : Nat}:
  match a b:
    case 0n b:
      {==}
    case 1n+x 0n:
      LBound.bnd.ft({Nat.sub(1n+x, 0n) == 0n : Nat}, h)
    case 1n+x 1n+y:
      tk.sub_le0(x, y, h)

# T less a d that is 0 is the text's bytes
def tk.st0(+T: Nat, d: Nat, +R: List<&2, Nat>, hd: {d == 0n : Nat}, tT: {T == Bound.bd_total(R) : Nat}) -> {Nat.sub(T, d) == Bound.bd_total(R) : Nat}:
  Equal.trans(Nat, Nat.sub(T, d), Nat.sub(T, 0n), Bound.bd_total(R), Equal.cong(Nat, Nat, z => Nat.sub(T, z), d, 0n, hd), Equal.trans(Nat, Nat.sub(T, 0n), T, Bound.bd_total(R), LBound.bnd.sub_zero(T), tT))

def tk.kq(+j: Nat, o: Bool) -> {Nat.is_le(1n+j, Bd.lines(1n+j, o)) == True{} : Bool}:
  match o:
    case False{}:
      LBound.bnd.le_refl(1n+j)
    case True{}:
      LBound.bnd.le_succ(1n+j)

# Lists
# -----

def tk.rev_snoc(a: List<&2, Nat>, +x: Nat) -> {Bound.bd_rev(List.append(&2, Nat, a, [x])) == x <> Bound.bd_rev(a) : List<&2, Nat>}:
  match a:
    case Nil{}:
      {==}
    case +h <> +t:
      Equal.cong(List<&2, Nat>, List<&2, Nat>, z => List.append(&2, Nat, z, [h]), Bound.bd_rev(List.append(&2, Nat, t, [x])), x <> Bound.bd_rev(t), tk.rev_snoc(t, x))

def tk.rev_rev(xs: List<&2, Nat>) -> {Bound.bd_rev(Bound.bd_rev(xs)) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case +x <> +r:
      Equal.trans(List<&2, Nat>, Bound.bd_rev(List.append(&2, Nat, Bound.bd_rev(r), [x])), x <> Bound.bd_rev(Bound.bd_rev(r)), x <> r, tk.rev_snoc(Bound.bd_rev(r), x), Equal.cong(List<&2, Nat>, List<&2, Nat>, z => x <> z, Bound.bd_rev(Bound.bd_rev(r)), r, tk.rev_rev(r)))

def tk.rev_then(+Z: List<&2, Nat>, +p: Nat, +ys: List<&2, Nat>) -> {Bound.bd_rev(Bound.bd_then(Z, p, ys)) == List.append(&2, Nat, Bound.bd_rev(ys), Bound.bd_glue(p, Bound.bd_rev(Z))) : List<&2, Nat>}:
  tk.rev_rev(List.append(&2, Nat, Bound.bd_rev(ys), Bound.bd_glue(p, Bound.bd_rev(Z))))

def tk.rev_kept(+xs: List<&2, Nat>, +m: Nat) -> {Bound.bd_rev(Bound.bd_kept(xs, m)) == Bound.bd_sfx(Bound.bd_rev(xs), m) : List<&2, Nat>}:
  tk.rev_rev(Bound.bd_sfx(Bound.bd_rev(xs), m))

def tk.glue0(xs: List<&2, Nat>) -> {Bound.bd_glue(0n, xs) == xs : List<&2, Nat>}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      {==}

def tk.lp_app(a: List<&2, Nat>, +ys: List<&2, Nat>, ha: {Bound.bd_lines_pos(a) == True{} : Bool}, hy: {Bound.bd_lines_pos(ys) == True{} : Bool}) -> {Bound.bd_lines_pos(List.append(&2, Nat, a, ys)) == True{} : Bool}:
  match a:
    case Nil{}:
      hy
    case h <> t:
      match h:
        case 0n:
          LBound.bnd.ft({Bound.bd_lines_pos(List.append(&2, Nat, 0n <> t, ys)) == True{} : Bool}, ha)
        case 1n++g:
          tk.lp_app(t, ys, ha, hy)

def tk.lp_rev(xs: List<&2, Nat>, h: {Bound.bd_lines_pos(xs) == True{} : Bool}) -> {Bound.bd_lines_pos(Bound.bd_rev(xs)) == True{} : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> +r:
      match x:
        case 0n:
          LBound.bnd.ft({Bound.bd_lines_pos(Bound.bd_rev(0n <> r)) == True{} : Bool}, h)
        case 1n++g:
          tk.lp_app(Bound.bd_rev(r), [1n+g], tk.lp_rev(r, h), {==})

# the last bytes of a text, as many as all its bytes, are all its lines
# (every line holds a byte)
def tk.sfx_all(R: List<&2, Nat>, lp: {Bound.bd_lines_pos(R) == True{} : Bool}) -> {Bound.bd_sfx(R, Bound.bd_total(R)) == R : List<&2, Nat>}:
  match R:
    case Nil{}:
      {==}
    case r <> +rest:
      match r:
        case 0n:
          LBound.bnd.ft({Bound.bd_sfx(0n <> rest, Bound.bd_total(0n <> rest)) == 0n <> rest : List<&2, Nat>}, lp)
        case 1n++g:
          +t = Bound.bd_total(rest)
          %Equal.sym(Bool, Nat.is_le(g, Nat.add(g, t)), True{}, tk.le_add(g, t)) : {Bound.bd_sfx.pick(_, 1n+g, 1n+Nat.add(g, t), Bound.bd_sfx(rest, Nat.sub(Nat.add(g, t), g))) == (1n+g) <> rest : List<&2, Nat>}
          %Equal.sym(Nat, Nat.sub(Nat.add(g, t), g), t, tk.add_sub_l(g, t)) : {(1n+g) <> Bound.bd_sfx(rest, _) == (1n+g) <> rest : List<&2, Nat>}
          Equal.cong(List<&2, Nat>, List<&2, Nat>, z => (1n+g) <> z, Bound.bd_sfx(rest, t), rest, tk.sfx_all(rest, lp))

# Fills
# -----

def tk.fill_zero(xs: List<&2, Nat>, +c: Nat) -> {Bd.fill(xs, 0n, c) == Bd.Win{0n, 0n} : Bd.Win}:
  match xs:
    case Nil{}:
      {==}
    case x <> rest:
      {==}

# Under bytes: what is kept holds more than the bytes the fill has left
# (c < p + S): the fill stops on a line before or at the piece of the
# line the kept end starts in, on both sides

def tk.gb.step(+r: Nat, +rest: List<&2, Nat>, +s: Nat, +p: Nat, +j: Nat, +c: Nat, ih: tk.If(Nat.is_lt(Nat.sub(c, Nat.add(p, r)), Nat.sub(1n+s, r)), {Bd.fill(Bound.bd_glue(0n, Bound.bd_sfx(rest, Nat.sub(1n+s, r))), j, Nat.sub(c, Nat.add(p, r))) == Bd.fill(Bound.bd_glue(0n, rest), j, Nat.sub(c, Nat.add(p, r))) : Bd.Win}), lt: {Nat.is_lt(c, Nat.add(p, 1n+s)) == True{} : Bool}, f2: Bool, e2: {Nat.is_le(Nat.add(p, r), c) == f2 : Bool}) -> {Bd.fill.pick(f2, Nat.add(p, r), Bd.fill(Bound.bd_sfx(rest, Nat.sub(1n+s, r)), j, Nat.sub(c, Nat.add(p, r)))) == Bd.fill.pick(f2, Nat.add(p, r), Bd.fill(rest, j, Nat.sub(c, Nat.add(p, r)))) : Bd.Win}:
  match f2:
    case True{}:
      +c2 = Nat.sub(c, Nat.add(p, r))
      +s2 = Nat.sub(1n+s, r)
      +lt2 = Equal.trans(Bool, Nat.is_lt(c2, s2), Nat.is_lt(c2, Nat.sub(Nat.add(p, 1n+s), Nat.add(p, r))), True{}, Equal.cong(Nat, Bool, z => Nat.is_lt(c2, z), s2, Nat.sub(Nat.add(p, 1n+s), Nat.add(p, r)), Equal.sym(Nat, Nat.sub(Nat.add(p, 1n+s), Nat.add(p, r)), s2, tk.sub_cancel(p, 1n+s, r))), tk.lt_sub(Nat.add(p, r), c, Nat.add(p, 1n+s), e2, lt))
      +eq0 = tk.use(Nat.is_lt(c2, s2), {Bd.fill(Bound.bd_glue(0n, Bound.bd_sfx(rest, s2)), j, c2) == Bd.fill(Bound.bd_glue(0n, rest), j, c2) : Bd.Win}, lt2, ih)
      +eq1 = Equal.trans(Bd.Win, Bd.fill(Bound.bd_sfx(rest, s2), j, c2), Bd.fill(Bound.bd_glue(0n, Bound.bd_sfx(rest, s2)), j, c2), Bd.fill(rest, j, c2), Equal.cong(List<&2, Nat>, Bd.Win, z => Bd.fill(z, j, c2), Bound.bd_sfx(rest, s2), Bound.bd_glue(0n, Bound.bd_sfx(rest, s2)), Equal.sym(List<&2, Nat>, Bound.bd_glue(0n, Bound.bd_sfx(rest, s2)), Bound.bd_sfx(rest, s2), tk.glue0(Bound.bd_sfx(rest, s2)))), Equal.trans(Bd.Win, Bd.fill(Bound.bd_glue(0n, Bound.bd_sfx(rest, s2)), j, c2), Bd.fill(Bound.bd_glue(0n, rest), j, c2), Bd.fill(rest, j, c2), eq0, Equal.cong(List<&2, Nat>, Bd.Win, z => Bd.fill(z, j, c2), Bound.bd_glue(0n, rest), rest, tk.glue0(rest))))
      Equal.cong(Bd.Win, Bd.Win, v => Bd.fill.more(Nat.add(p, r), v), Bd.fill(Bound.bd_sfx(rest, s2), j, c2), Bd.fill(rest, j, c2), eq1)
    case False{}:
      {==}

def tk.gb.pick(+r: Nat, +rest: List<&2, Nat>, +s: Nat, +p: Nat, +j: Nat, +c: Nat, ih: tk.If(Nat.is_lt(Nat.sub(c, Nat.add(p, r)), Nat.sub(1n+s, r)), {Bd.fill(Bound.bd_glue(0n, Bound.bd_sfx(rest, Nat.sub(1n+s, r))), j, Nat.sub(c, Nat.add(p, r))) == Bd.fill(Bound.bd_glue(0n, rest), j, Nat.sub(c, Nat.add(p, r))) : Bd.Win}), +lt: {Nat.is_lt(c, Nat.add(p, 1n+s)) == True{} : Bool}, fits: Bool, e: {Nat.is_le(r, 1n+s) == fits : Bool}) -> {Bd.fill(Bound.bd_glue(p, Bound.bd_sfx.pick(fits, r, 1n+s, Bound.bd_sfx(rest, Nat.sub(1n+s, r)))), 1n+j, c) == Bd.fill(Nat.add(p, r) <> rest, 1n+j, c) : Bd.Win}:
  match fits:
    case True{}:
      tk.gb.step(r, rest, s, p, j, c, ih, lt, Nat.is_le(Nat.add(p, r), c), {==})
    case False{}:
      +nf = tk.lt_nle(c, Nat.add(p, 1n+s), lt)
      +nr = tk.lt_nle(c, Nat.add(p, r), tk.lt_trans(c, Nat.add(p, 1n+s), Nat.add(p, r), lt, tk.add_lt_mono(p, 1n+s, r, tk.nle_lt(r, 1n+s, e))))
      %Equal.sym(Bool, Nat.is_le(Nat.add(p, 1n+s), c), False{}, nf) : {Bd.fill.pick(_, Nat.add(p, 1n+s), Bd.fill(Nil{}, j, Nat.sub(c, Nat.add(p, 1n+s)))) == Bd.fill.pick(Nat.is_le(Nat.add(p, r), c), Nat.add(p, r), Bd.fill(rest, j, Nat.sub(c, Nat.add(p, r)))) : Bd.Win}
      %Equal.sym(Bool, Nat.is_le(Nat.add(p, r), c), False{}, nr) : {Bd.fill.pick(False{}, Nat.add(p, 1n+s), Bd.fill(Nil{}, j, Nat.sub(c, Nat.add(p, 1n+s)))) == Bd.fill.pick(_, Nat.add(p, r), Bd.fill(rest, j, Nat.sub(c, Nat.add(p, r)))) : Bd.Win}
      {==}

def tk.gb.go(+r: Nat, +rest: List<&2, Nat>, +s: Nat, +p: Nat, +j: Nat, +c: Nat, ih: tk.If(Nat.is_lt(Nat.sub(c, Nat.add(p, r)), Nat.sub(1n+s, r)), {Bd.fill(Bound.bd_glue(0n, Bound.bd_sfx(rest, Nat.sub(1n+s, r))), j, Nat.sub(c, Nat.add(p, r))) == Bd.fill(Bound.bd_glue(0n, rest), j, Nat.sub(c, Nat.add(p, r))) : Bd.Win}), hb: Bool, eh: {Nat.is_lt(c, Nat.add(p, 1n+s)) == hb : Bool}) -> tk.If(hb, {Bd.fill(Bound.bd_glue(p, Bound.bd_sfx(r <> rest, 1n+s)), 1n+j, c) == Bd.fill(Bound.bd_glue(p, r <> rest), 1n+j, c) : Bd.Win}):
  match hb:
    case True{}:
      tk.gb.pick(r, rest, s, p, j, c, ih, eh, Nat.is_le(r, 1n+s), {==})
    case False{}:
      Unit{}

def tk.gb.z(+r: Nat, +rest: List<&2, Nat>, +p: Nat, n: Nat, +c: Nat, hb: Bool, eh: {Nat.is_lt(c, Nat.add(p, 0n)) == hb : Bool}) -> tk.If(hb, {Bd.fill(Bound.bd_glue(p, Bound.bd_sfx(r <> rest, 0n)), n, c) == Bd.fill(Bound.bd_glue(p, r <> rest), n, c) : Bd.Win}):
  match n:
    case 0n:
      tk.mk(hb, {Bd.fill(Bound.bd_glue(p, Bound.bd_sfx(r <> rest, 0n)), 0n, c) == Bd.fill(Bound.bd_glue(p, r <> rest), 0n, c) : Bd.Win}, {==})
    case 1n++j:
      match hb:
        case True{}:
          +nr = tk.lt_nle(c, Nat.add(p, r), tk.lt_le(c, Nat.add(p, 0n), Nat.add(p, r), eh, LBound.bnd.le_add_mono(p, 0n, r, LBound.bnd.le0(r))))
          %Equal.sym(Bool, Nat.is_le(Nat.add(p, r), c), False{}, nr) : {Bd.Win{0n, 0n} == Bd.fill.pick(_, Nat.add(p, r), Bd.fill(rest, j, Nat.sub(c, Nat.add(p, r)))) : Bd.Win}
          {==}
        case False{}:
          Unit{}

# the fill of what is kept (the end of the text from S bytes, its first
# line glued to p bytes) is the fill of the whole text, when that end
# holds more than the bytes the fill has left
def tk.gb(R: List<&2, Nat>, S: Nat, +p: Nat, n: Nat, +c: Nat, hb: Bool, eh: {Nat.is_lt(c, Nat.add(p, S)) == hb : Bool}) -> tk.If(hb, {Bd.fill(Bound.bd_glue(p, Bound.bd_sfx(R, S)), n, c) == Bd.fill(Bound.bd_glue(p, R), n, c) : Bd.Win}):
  match R:
    case Nil{}:
      tk.mk(hb, {Bd.fill(Bound.bd_glue(p, Bound.bd_sfx(Nil{}, S)), n, c) == Bd.fill(Bound.bd_glue(p, Nil{}), n, c) : Bd.Win}, {==})
    case +r <> +rest:
      match S:
        case 0n:
          tk.gb.z(r, rest, p, n, c, hb, eh)
        case 1n++s:
          match n:
            case 0n:
              tk.mk(hb, {Bd.fill(Bound.bd_glue(p, Bound.bd_sfx(r <> rest, 1n+s)), 0n, c) == Bd.fill(Bound.bd_glue(p, r <> rest), 0n, c) : Bd.Win}, tk.fill_zero(Bound.bd_glue(p, Bound.bd_sfx(r <> rest, 1n+s)), c))
            case 1n++j:
              ih = tk.gb(rest, Nat.sub(1n+s, r), 0n, j, Nat.sub(c, Nat.add(p, r)), Nat.is_lt(Nat.sub(c, Nat.add(p, r)), Nat.sub(1n+s, r)), {==})
              tk.gb.go(r, rest, s, p, j, c, ih, hb, eh)

# the later output's lines come first (from the end): the fill reads them
# alike on both sides, then the kept end
def tk.fyb(Y: List<&2, Nat>, +R: List<&2, Nat>, +S: Nat, +p: Nat, n: Nat, +c: Nat, lt: {Nat.is_lt(c, Nat.add(p, S)) == True{} : Bool}) -> {Bd.fill(List.append(&2, Nat, Y, Bound.bd_glue(p, Bound.bd_sfx(R, S))), n, c) == Bd.fill(List.append(&2, Nat, Y, Bound.bd_glue(p, R)), n, c) : Bd.Win}:
  match Y:
    case Nil{}:
      tk.use(Nat.is_lt(c, Nat.add(p, S)), {Bd.fill(Bound.bd_glue(p, Bound.bd_sfx(R, S)), n, c) == Bd.fill(Bound.bd_glue(p, R), n, c) : Bd.Win}, lt, tk.gb(R, S, p, n, c, Nat.is_lt(c, Nat.add(p, S)), {==}))
    case +y <> +ys:
      match n:
        case 0n:
          {==}
        case 1n++j:
          Equal.cong(Bd.Win, Bd.Win, v => Bd.fill.pick(Nat.is_le(y, c), y, v), Bd.fill(List.append(&2, Nat, ys, Bound.bd_glue(p, Bound.bd_sfx(R, S))), j, Nat.sub(c, y)), Bd.fill(List.append(&2, Nat, ys, Bound.bd_glue(p, R)), j, Nat.sub(c, y)), tk.fyb(ys, R, S, p, j, Nat.sub(c, y), tk.le_lt(Nat.sub(c, y), c, Nat.add(p, S), LBound.bnd.sub_le(c, y), lt)))

# Under lines: what is kept holds the last q lines whole and a byte of the
# line before (the end mline reads), and the fill takes at most q lines

# the claim for a kept end m: none when there is none; else that end
# holds a byte and the fill of it (after the later lines Y) is the fill of
# the whole text
def tk.LGY(m: Maybe<&2, Nat>, R: List<&2, Nat>, Y: List<&2, Nat>, p: Nat, n: Nat, c: Nat) -> Type:
  match m:
    case None{}:
      Unit
    case Some{+v}:
      {Nat.is_lt(0n, v) == True{} : Bool} & {Bd.fill(List.append(&2, Nat, Y, Bound.bd_glue(p, Bound.bd_sfx(R, v))), n, c) == Bd.fill(List.append(&2, Nat, Y, Bound.bd_glue(p, R)), n, c) : Bd.Win}

def tk.gl.eq(+r: Nat, +rest: List<&2, Nat>, +p: Nat, +j: Nat, +c: Nat, +u: Nat, eq: {Bd.fill(List.append(&2, Nat, Nil{}, Bound.bd_glue(0n, Bound.bd_sfx(rest, 1n+u))), j, Nat.sub(c, Nat.add(p, r))) == Bd.fill(List.append(&2, Nat, Nil{}, Bound.bd_glue(0n, rest)), j, Nat.sub(c, Nat.add(p, r))) : Bd.Win}) -> {Bd.fill(Bound.bd_glue(p, Bound.bd_sfx(r <> rest, Nat.add(r, 1n+u))), 1n+j, c) == Bd.fill(Bound.bd_glue(p, r <> rest), 1n+j, c) : Bd.Win}:
  +c2 = Nat.sub(c, Nat.add(p, r))
  +le = LBound.bnd.le_trans(r, Nat.add(r, u), 1n+Nat.add(r, u), tk.le_add(r, u), LBound.bnd.le_succ(Nat.add(r, u)))
  +eq1 = Equal.trans(Bd.Win, Bd.fill(Bound.bd_sfx(rest, 1n+u), j, c2), Bd.fill(Bound.bd_glue(0n, Bound.bd_sfx(rest, 1n+u)), j, c2), Bd.fill(rest, j, c2), Equal.cong(List<&2, Nat>, Bd.Win, z => Bd.fill(z, j, c2), Bound.bd_sfx(rest, 1n+u), Bound.bd_glue(0n, Bound.bd_sfx(rest, 1n+u)), Equal.sym(List<&2, Nat>, Bound.bd_glue(0n, Bound.bd_sfx(rest, 1n+u)), Bound.bd_sfx(rest, 1n+u), tk.glue0(Bound.bd_sfx(rest, 1n+u)))), Equal.trans(Bd.Win, Bd.fill(Bound.bd_glue(0n, Bound.bd_sfx(rest, 1n+u)), j, c2), Bd.fill(Bound.bd_glue(0n, rest), j, c2), Bd.fill(rest, j, c2), eq, Equal.cong(List<&2, Nat>, Bd.Win, z => Bd.fill(z, j, c2), Bound.bd_glue(0n, rest), rest, tk.glue0(rest))))
  %Equal.sym(Nat, Nat.add(r, 1n+u), 1n+Nat.add(r, u), LBound.bnd.add_succ(r, u)) : {Bd.fill(Bound.bd_glue(p, Bound.bd_sfx(r <> rest, _)), 1n+j, c) == Bd.fill(Nat.add(p, r) <> rest, 1n+j, c) : Bd.Win}
  %Equal.sym(Bool, Nat.is_le(r, 1n+Nat.add(r, u)), True{}, le) : {Bd.fill(Bound.bd_glue(p, Bound.bd_sfx.pick(_, r, 1n+Nat.add(r, u), Bound.bd_sfx(rest, Nat.sub(1n+Nat.add(r, u), r)))), 1n+j, c) == Bd.fill(Nat.add(p, r) <> rest, 1n+j, c) : Bd.Win}
  %Equal.sym(Nat, Nat.sub(1n+Nat.add(r, u), r), 1n+u, tk.sub_succ_add(r, u)) : {Bd.fill(Bound.bd_glue(p, r <> Bound.bd_sfx(rest, _)), 1n+j, c) == Bd.fill(Nat.add(p, r) <> rest, 1n+j, c) : Bd.Win}
  Equal.cong(Bd.Win, Bd.Win, v => Bd.fill.pick(Nat.is_le(Nat.add(p, r), c), Nat.add(p, r), v), Bd.fill(Bound.bd_sfx(rest, 1n+u), j, c2), Bd.fill(rest, j, c2), eq1)

def tk.gl.v(+r: Nat, +rest: List<&2, Nat>, +p: Nat, +j: Nat, +c: Nat, v: Nat, ih: tk.LGY(Some{v}, rest, Nil{}, 0n, j, Nat.sub(c, Nat.add(p, r)))) -> tk.LGY(Some{Nat.add(r, v)}, r <> rest, Nil{}, p, 1n+j, c):
  match v:
    case 0n:
      (pos, eq) = ih
      LBound.bnd.ft(tk.LGY(Some{Nat.add(r, 0n)}, r <> rest, Nil{}, p, 1n+j, c), pos)
    case 1n++u:
      (pos, eq) = ih
      (tk.pos_add(r, u), tk.gl.eq(r, rest, p, j, c, u, eq))

def tk.gl.s(m: Maybe<&2, Nat>, +r: Nat, +rest: List<&2, Nat>, +p: Nat, +j: Nat, +c: Nat, ih: tk.LGY(m, rest, Nil{}, 0n, j, Nat.sub(c, Nat.add(p, r)))) -> tk.LGY(Bd.mline.add(r, m), r <> rest, Nil{}, p, 1n+j, c):
  match m:
    case None{}:
      Unit{}
    case Some{+v}:
      tk.gl.v(r, rest, p, j, c, v, ih)

def tk.gl.z(m: Maybe<&2, Nat>, +r: Nat, +rest: List<&2, Nat>, +p: Nat, +c: Nat, ih: tk.LGY(m, rest, Nil{}, 0n, 0n, c)) -> tk.LGY(Bd.mline.add(r, m), r <> rest, Nil{}, p, 0n, c):
  match m:
    case None{}:
      Unit{}
    case Some{+v}:
      (pos, eq) = ih
      (tk.pos_add2(r, v, pos), tk.fill_zero(Bound.bd_glue(p, Bound.bd_sfx(r <> rest, Nat.add(r, v))), c))

# the kept end mline reads (the last q lines and a byte), its first line
# glued to p bytes: the fill of at most q lines reads the same lines
def tk.gl(R: List<&2, Nat>, q: Nat, +p: Nat, n: Nat, +c: Nat, nq: {Nat.is_le(n, q) == True{} : Bool}) -> tk.LGY(Bd.mline(R, q), R, Nil{}, p, n, c):
  match R:
    case Nil{}:
      Unit{}
    case +r <> +rest:
      match q:
        case 0n:
          match n:
            case 0n:
              ({==}, tk.fill_zero(Bound.bd_glue(p, Bound.bd_sfx(r <> rest, 1n)), c))
            case 1n++j:
              LBound.bnd.ft(tk.LGY(Some{1n}, r <> rest, Nil{}, p, 1n+j, c), nq)
        case 1n++q2:
          match n:
            case 0n:
              tk.gl.z(Bd.mline(rest, q2), r, rest, p, c, tk.gl(rest, q2, 0n, 0n, c, LBound.bnd.le0(q2)))
            case 1n++j:
              tk.gl.s(Bd.mline(rest, q2), r, rest, p, j, c, tk.gl(rest, q2, 0n, j, Nat.sub(c, Nat.add(p, r)), nq))

def tk.fyl.z(m: Maybe<&2, Nat>, +R: List<&2, Nat>, +y: Nat, +ys: List<&2, Nat>, +p: Nat, +c: Nat, ih: tk.LGY(m, R, ys, p, 0n, c)) -> tk.LGY(m, R, y <> ys, p, 0n, c):
  match m:
    case None{}:
      Unit{}
    case Some{+v}:
      (pos, eq) = ih
      (pos, {==})

def tk.fyl.s(m: Maybe<&2, Nat>, +R: List<&2, Nat>, +y: Nat, +ys: List<&2, Nat>, +p: Nat, +j: Nat, +c: Nat, ih: tk.LGY(m, R, ys, p, j, Nat.sub(c, y))) -> tk.LGY(m, R, y <> ys, p, 1n+j, c):
  match m:
    case None{}:
      Unit{}
    case Some{+v}:
      (pos, eq) = ih
      (pos, Equal.cong(Bd.Win, Bd.Win, w => Bd.fill.pick(Nat.is_le(y, c), y, w), Bd.fill(List.append(&2, Nat, ys, Bound.bd_glue(p, Bound.bd_sfx(R, v))), j, Nat.sub(c, y)), Bd.fill(List.append(&2, Nat, ys, Bound.bd_glue(p, R)), j, Nat.sub(c, y)), eq))

def tk.fyl(Y: List<&2, Nat>, +R: List<&2, Nat>, +q: Nat, +p: Nat, n: Nat, +c: Nat, nq: {Nat.is_le(n, q) == True{} : Bool}) -> tk.LGY(Bd.mline(R, q), R, Y, p, n, c):
  match Y:
    case Nil{}:
      tk.gl(R, q, p, n, c, nq)
    case +y <> +ys:
      match n:
        case 0n:
          tk.fyl.z(Bd.mline(R, q), R, y, ys, p, c, tk.fyl(ys, R, q, p, 0n, c, LBound.bnd.le0(q)))
        case 1n++j:
          tk.fyl.s(Bd.mline(R, q), R, y, ys, p, j, c, tk.fyl(ys, R, q, p, j, Nat.sub(c, y), LBound.bnd.le_trans(j, 1n+j, q, LBound.bnd.le_succ(j), nq)))

# The window
# ----------

def tk.nil(xs: List<&2, Nat>) -> Bool:
  match xs:
    case Nil{}:
      True{}
    case x <> r:
      False{}

def tk.nil_app(Y: List<&2, Nat>, +X1: List<&2, Nat>, +X2: List<&2, Nat>, h: {tk.nil(X1) == tk.nil(X2) : Bool}) -> {tk.nil(List.append(&2, Nat, Y, X1)) == tk.nil(List.append(&2, Nat, Y, X2)) : Bool}:
  match Y:
    case Nil{}:
      h
    case y <> ys:
      {==}

def tk.nil_glue(+p: Nat, xs: List<&2, Nat>) -> {tk.nil(Bound.bd_glue(p, xs)) == tk.nil(xs) : Bool}:
  match xs:
    case Nil{}:
      {==}
    case x <> r:
      {==}

def tk.nil_pick(fits: Bool, +r: Nat, +m: Nat, more: List<&2, Nat>) -> {tk.nil(Bound.bd_sfx.pick(fits, r, m, more)) == False{} : Bool}:
  match fits:
    case True{}:
      {==}
    case False{}:
      {==}

def tk.nil_sfx(R: List<&2, Nat>, +s: Nat) -> {tk.nil(Bound.bd_sfx(R, 1n+s)) == tk.nil(R) : Bool}:
  match R:
    case Nil{}:
      {==}
    case +r <> +rest:
      tk.nil_pick(Nat.is_le(r, 1n+s), r, 1n+s, Bound.bd_sfx(rest, Nat.sub(1n+s, r)))

def tk.nil_e(+R: List<&2, Nat>, +s: Nat, +Y: List<&2, Nat>, +p: Nat) -> {tk.nil(List.append(&2, Nat, Y, Bound.bd_glue(p, Bound.bd_sfx(R, 1n+s)))) == tk.nil(List.append(&2, Nat, Y, Bound.bd_glue(p, R))) : Bool}:
  tk.nil_app(Y, Bound.bd_glue(p, Bound.bd_sfx(R, 1n+s)), Bound.bd_glue(p, R), Equal.trans(Bool, tk.nil(Bound.bd_glue(p, Bound.bd_sfx(R, 1n+s))), tk.nil(Bound.bd_sfx(R, 1n+s)), tk.nil(Bound.bd_glue(p, R)), tk.nil_glue(p, Bound.bd_sfx(R, 1n+s)), Equal.trans(Bool, tk.nil(Bound.bd_sfx(R, 1n+s)), tk.nil(R), tk.nil(Bound.bd_glue(p, R)), tk.nil_sfx(R, s), Equal.sym(Bool, tk.nil(Bound.bd_glue(p, R)), tk.nil(R), tk.nil_glue(p, R)))))

def tk.knone(A: List<&2, Nat>, B: List<&2, Nat>, +w: Nat, h: {tk.nil(A) == tk.nil(B) : Bool}) -> {Bd.keep.none(A, w) == Bd.keep.none(B, w) : Bd.Win}:
  match A:
    case Nil{}:
      match B:
        case Nil{}:
          {==}
        case y <> ys:
          LBound.bnd.tf({Bd.keep.none(Nil{}, w) == Bd.keep.none(y <> ys, w) : Bd.Win}, h)
    case x <> xs:
      match B:
        case Nil{}:
          LBound.bnd.ft({Bd.keep.none(x <> xs, w) == Bd.keep.none(Nil{}, w) : Bd.Win}, h)
        case y <> ys:
          {==}

def tk.kof(W: Bd.Win, +A: List<&2, Nat>, +B: List<&2, Nat>, +w: Nat, h: {tk.nil(A) == tk.nil(B) : Bool}) -> {Bd.keep.of(W, A, w) == Bd.keep.of(W, B, w) : Bd.Win}:
  match W:
    case Bd.Win{b, l}:
      match l:
        case 0n:
          tk.knone(A, B, w, h)
        case 1n++m:
          {==}

def tk.keep_eq(+A: List<&2, Nat>, +B: List<&2, Nat>, +j: Nat, +q: Nat, +w: Nat, eqF: {Bd.fill(A, 1n+j, 1n+q) == Bd.fill(B, 1n+j, 1n+q) : Bd.Win}, nilE: {tk.nil(A) == tk.nil(B) : Bool}) -> {Bd.keep(A, 1n+j, 1n+q, w) == Bd.keep(B, 1n+j, 1n+q, w) : Bd.Win}:
  %Equal.sym(Bd.Win, Bd.fill(A, 1n+j, 1n+q), Bd.fill(B, 1n+j, 1n+q), eqF) : {Bd.keep.of(_, A, w) == Bd.keep.of(Bd.fill(B, 1n+j, 1n+q), B, w) : Bd.Win}
  tk.kof(Bd.fill(B, 1n+j, 1n+q), A, B, w, nilE)

# the window of what is kept then Y is the window of the text then Y
def tk.G(R: List<&2, Nat>, S: Nat, Y: List<&2, Nat>, p: Nat, k: Nat, b: Nat, w: Nat) -> Type:
  {Bd.keep(List.append(&2, Nat, Y, Bound.bd_glue(p, Bound.bd_sfx(R, S))), k, b, w) == Bd.keep(List.append(&2, Nat, Y, Bound.bd_glue(p, R)), k, b, w) : Bd.Win}

# kept whole
def tk.core_full(+R: List<&2, Nat>, +S: Nat, +Y: List<&2, Nat>, +p: Nat, +k: Nat, +b: Nat, +w: Nat, e: {S == Bound.bd_total(R) : Nat}, lp: {Bound.bd_lines_pos(R) == True{} : Bool}) -> tk.G(R, S, Y, p, k, b, w):
  Equal.cong(List<&2, Nat>, Bd.Win, z => Bd.keep(List.append(&2, Nat, Y, Bound.bd_glue(p, z)), k, b, w), Bound.bd_sfx(R, S), R, Equal.trans(List<&2, Nat>, Bound.bd_sfx(R, S), Bound.bd_sfx(R, Bound.bd_total(R)), R, Equal.cong(Nat, List<&2, Nat>, z => Bound.bd_sfx(R, z), S, Bound.bd_total(R), e), tk.sfx_all(R, lp)))

# kept: more than the cap's bytes
def tk.core_bytes(+j: Nat, +q0: Nat, S: Nat, +R: List<&2, Nat>, +Y: List<&2, Nat>, +p: Nat, +w: Nat, lt: {Nat.is_lt(1n+q0, S) == True{} : Bool}) -> tk.G(R, S, Y, p, 1n+j, 1n+q0, w):
  match S:
    case 0n:
      LBound.bnd.ft(tk.G(R, 0n, Y, p, 1n+j, 1n+q0, w), lt)
    case 1n++s:
      +lt2 = tk.lt_le(1n+q0, 1n+s, Nat.add(p, 1n+s), lt, tk.le_addl(p, 1n+s))
      tk.keep_eq(List.append(&2, Nat, Y, Bound.bd_glue(p, Bound.bd_sfx(R, 1n+s))), List.append(&2, Nat, Y, Bound.bd_glue(p, R)), j, q0, w, tk.fyb(Y, R, 1n+s, p, 1n+j, 1n+q0, lt2), tk.nil_e(R, s, Y, p))

# kept: the last lines (at least the cap's) and a byte
def tk.core_v(+j: Nat, +q0: Nat, v: Nat, +R: List<&2, Nat>, +Y: List<&2, Nat>, +p: Nat, +w: Nat, lg: tk.LGY(Some{v}, R, Y, p, 1n+j, 1n+q0)) -> tk.G(R, v, Y, p, 1n+j, 1n+q0, w):
  match v:
    case 0n:
      (pos, eq) = lg
      LBound.bnd.ft(tk.G(R, 0n, Y, p, 1n+j, 1n+q0, w), pos)
    case 1n++s:
      (pos, eq) = lg
      tk.keep_eq(List.append(&2, Nat, Y, Bound.bd_glue(p, Bound.bd_sfx(R, 1n+s))), List.append(&2, Nat, Y, Bound.bd_glue(p, R)), j, q0, w, eq, tk.nil_e(R, s, Y, p))

# The margin's cases
# ------------------

def tk.case_v(+j: Nat, +q0: Nat, +R: List<&2, Nat>, +Y: List<&2, Nat>, +p: Nat, +w: Nat, +T: Nat, +v: Nat, tT: {T == Bound.bd_total(R) : Nat}, lp: {Bound.bd_lines_pos(R) == True{} : Bool}, lgy: tk.LGY(Some{v}, R, Y, p, 1n+j, 1n+q0), le: Bool, e: {Nat.is_le(v, T) == le : Bool}) -> tk.G(R, Nat.sub(T, Nat.sub(T, v)), Y, p, 1n+j, 1n+q0, w):
  match le:
    case True{}:
      %Equal.sym(Nat, Nat.sub(T, Nat.sub(T, v)), v, LBound.bnd.sub_sub(T, v, e)) : tk.G(R, _, Y, p, 1n+j, 1n+q0, w)
      tk.core_v(j, q0, v, R, Y, p, w, lgy)
    case False{}:
      tk.core_full(R, Nat.sub(T, Nat.sub(T, v)), Y, p, 1n+j, 1n+q0, w, tk.st0(T, Nat.sub(T, v), R, tk.sub_le0(T, v, LBound.bnd.nle_le(v, T, e)), tT), lp)

def tk.case_ml(mv: Maybe<&2, Nat>, +j: Nat, +q0: Nat, +R: List<&2, Nat>, +Y: List<&2, Nat>, +p: Nat, +w: Nat, +T: Nat, tT: {T == Bound.bd_total(R) : Nat}, lp: {Bound.bd_lines_pos(R) == True{} : Bool}, lgy: tk.LGY(mv, R, Y, p, 1n+j, 1n+q0)) -> tk.G(R, Nat.sub(T, Nat.sub(T, Bd.margin.lines(mv, T))), Y, p, 1n+j, 1n+q0, w):
  match mv:
    case None{}:
      tk.core_full(R, Nat.sub(T, Nat.sub(T, T)), Y, p, 1n+j, 1n+q0, w, tk.st0(T, Nat.sub(T, T), R, LBound.bnd.sub_self(T), tT), lp)
    case Some{+v}:
      tk.case_v(j, q0, R, Y, p, w, T, v, tT, lp, lgy, Nat.is_le(v, T), {==})

def tk.case_in(+j: Nat, +q0: Nat, +R: List<&2, Nat>, +Y: List<&2, Nat>, +p: Nat, +w: Nat, +T: Nat, +mc: Nat, tT: {T == Bound.bd_total(R) : Nat}, lp: {Bound.bd_lines_pos(R) == True{} : Bool}, lt: {Nat.is_lt(1n+q0, mc) == True{} : Bool}, le: Bool, e: {Nat.is_le(mc, T) == le : Bool}) -> tk.G(R, Nat.sub(T, Nat.sub(T, mc)), Y, p, 1n+j, 1n+q0, w):
  match le:
    case True{}:
      %Equal.sym(Nat, Nat.sub(T, Nat.sub(T, mc)), mc, LBound.bnd.sub_sub(T, mc, e)) : tk.G(R, _, Y, p, 1n+j, 1n+q0, w)
      tk.core_bytes(j, q0, mc, R, Y, p, w, lt)
    case False{}:
      tk.core_full(R, Nat.sub(T, Nat.sub(T, mc)), Y, p, 1n+j, 1n+q0, w, tk.st0(T, Nat.sub(T, mc), R, tk.sub_le0(T, mc, LBound.bnd.nle_le(mc, T, e)), tT), lp)

def tk.case_mc(+j: Nat, +q0: Nat, +R: List<&2, Nat>, +Y: List<&2, Nat>, +p: Nat, +w: Nat, +T: Nat, +mc: Nat, tT: {T == Bound.bd_total(R) : Nat}, lp: {Bound.bd_lines_pos(R) == True{} : Bool}, lt: Bool, e: {Nat.is_lt(1n+q0, mc) == lt : Bool}, past: {Bool.or(lt, Nat.is_le(T, mc)) == True{} : Bool}) -> tk.G(R, Nat.sub(T, Nat.sub(T, mc)), Y, p, 1n+j, 1n+q0, w):
  match lt:
    case True{}:
      tk.case_in(j, q0, R, Y, p, w, T, mc, tT, lp, e, Nat.is_le(mc, T), {==})
    case False{}:
      tk.core_full(R, Nat.sub(T, Nat.sub(T, mc)), Y, p, 1n+j, 1n+q0, w, tk.st0(T, Nat.sub(T, mc), R, tk.sub_le0(T, mc, past), tT), lp)

def tk.case(+j: Nat, +q0: Nat, +R: List<&2, Nat>, +Y: List<&2, Nat>, +p: Nat, +w: Nat, +T: Nat, +mc: Nat, +mv: Maybe<&2, Nat>, tT: {T == Bound.bd_total(R) : Nat}, lp: {Bound.bd_lines_pos(R) == True{} : Bool}, past: {Bool.or(Nat.is_lt(1n+q0, mc), Nat.is_le(T, mc)) == True{} : Bool}, lgy: tk.LGY(mv, R, Y, p, 1n+j, 1n+q0), le: Bool, e: {Nat.is_le(mc, Bd.margin.lines(mv, T)) == le : Bool}) -> tk.G(R, Nat.sub(T, Nat.sub(T, Bd.least.pick(le, mc, Bd.margin.lines(mv, T)))), Y, p, 1n+j, 1n+q0, w):
  match le:
    case True{}:
      tk.case_mc(j, q0, R, Y, p, w, T, mc, tT, lp, Nat.is_lt(1n+q0, mc), {==}, past)
    case False{}:
      tk.case_ml(mv, j, q0, R, Y, p, w, T, tT, lp, lgy)

# The stream
# ----------

# the bytes a tail stores after a look: the text's less the cut
def tk.stored(w0: Bd.Win, +j: Nat, +q0: Nat, +bs: Nat, +nl: Nat, +op: Bool, +x: Bd.Body, +len: Nat) -> {Bound.bd_st_stored(Bound.bd_fst.look(Bd.look.of(Bd.Cap{1n+q0, 1n+j, True{}}, bs, nl, op, x, len, w0))) == Nat.sub(len, Nat.sub(len, Bd.margin(Bd.Cap{1n+q0, 1n+j, True{}}, x))) : Nat}:
  match w0:
    case Bd.Win{kb, kl}:
      {==}

# a tail window of a text Z then p bytes then ys reads Z from its end
def tk.win(+Z: List<&2, Nat>, +p: Nat, +ys: List<&2, Nat>, +j: Nat, +q0: Nat, +o2: Bool, +h2: Nat, +w: Nat, +m2: Nat) -> {Bd.window(Bd.Cap{1n+q0, 1n+j, True{}}, Bd.Body{Bound.bd_then(Z, p, ys), o2, h2, w, m2}) == Bd.keep(List.append(&2, Nat, Bound.bd_rev(ys), Bound.bd_glue(p, Bound.bd_rev(Z))), 1n+j, 1n+q0, w) : Bd.Win}:
  Equal.cong(List<&2, Nat>, Bd.Win, z => Bd.keep(z, 1n+j, 1n+q0, w), List.reverse(&2, Nat, Bound.bd_then(Z, p, ys)), List.append(&2, Nat, Bound.bd_rev(ys), Bound.bd_glue(p, Bound.bd_rev(Z))), Equal.trans(List<&2, Nat>, List.reverse(&2, Nat, Bound.bd_then(Z, p, ys)), Bound.bd_rev(Bound.bd_then(Z, p, ys)), List.append(&2, Nat, Bound.bd_rev(ys), Bound.bd_glue(p, Bound.bd_rev(Z))), LBound.bnd.rev(Bound.bd_then(Z, p, ys)), tk.rev_then(Z, p, ys)))

def tk.wineq(+Z1: List<&2, Nat>, +Z2: List<&2, Nat>, +p: Nat, +ys: List<&2, Nat>, +j: Nat, +q0: Nat, +o2: Bool, +h2: Nat, +w: Nat, +m2: Nat, h: {Bd.keep(List.append(&2, Nat, Bound.bd_rev(ys), Bound.bd_glue(p, Bound.bd_rev(Z1))), 1n+j, 1n+q0, w) == Bd.keep(List.append(&2, Nat, Bound.bd_rev(ys), Bound.bd_glue(p, Bound.bd_rev(Z2))), 1n+j, 1n+q0, w) : Bd.Win}) -> {Bd.window(Bd.Cap{1n+q0, 1n+j, True{}}, Bd.Body{Bound.bd_then(Z1, p, ys), o2, h2, w, m2}) == Bd.window(Bd.Cap{1n+q0, 1n+j, True{}}, Bd.Body{Bound.bd_then(Z2, p, ys), o2, h2, w, m2}) : Bd.Win}:
  +W1 = Bd.window(Bd.Cap{1n+q0, 1n+j, True{}}, Bd.Body{Bound.bd_then(Z1, p, ys), o2, h2, w, m2})
  +W2 = Bd.window(Bd.Cap{1n+q0, 1n+j, True{}}, Bd.Body{Bound.bd_then(Z2, p, ys), o2, h2, w, m2})
  +K1 = Bd.keep(List.append(&2, Nat, Bound.bd_rev(ys), Bound.bd_glue(p, Bound.bd_rev(Z1))), 1n+j, 1n+q0, w)
  +K2 = Bd.keep(List.append(&2, Nat, Bound.bd_rev(ys), Bound.bd_glue(p, Bound.bd_rev(Z2))), 1n+j, 1n+q0, w)
  Equal.trans(Bd.Win, W1, K1, W2, tk.win(Z1, p, ys, j, q0, o2, h2, w, m2), Equal.trans(Bd.Win, K1, K2, W2, h, Equal.sym(Bd.Win, W2, K2, tk.win(Z2, p, ys, j, q0, o2, h2, w, m2))))

def tk.main(+j: Nat, +q0: Nat, +bs: Nat, +nl: Nat, +op: Bool, +sd: Nat, +xs: List<&2, Nat>, +o: Bool, +hc: Nat, +tc: Nat, +mc: Nat, +p: Nat, +ys: List<&2, Nat>, +o2: Bool, +h2: Nat, +w: Nat, +m2: Nat, full: {Bound.bd_lines_pos(xs) == True{} : Bool}, past: {Bool.or(Nat.is_lt(1n+q0, mc), Nat.is_le(Bound.bd_total(xs), mc)) == True{} : Bool}) -> {Bd.window(Bd.Cap{1n+q0, 1n+j, True{}}, Bd.Body{Bound.bd_then(Bound.bd_kept(xs, Bound.bd_st_stored(Bound.bd_fst.look(Bd.look(Bd.St{Bd.Cap{1n+q0, 1n+j, True{}}, bs, nl, op, sd}, Bd.Body{xs, o, hc, tc, mc})))), p, ys), o2, h2, w, m2}) == Bd.window(Bd.Cap{1n+q0, 1n+j, True{}}, Bd.Body{Bound.bd_then(xs, p, ys), o2, h2, w, m2}) : Bd.Win}:
  +c = {Bd.Cap{1n+q0, 1n+j, True{}} : Bd.Cap}
  +x = {Bd.Body{xs, o, hc, tc, mc} : Bd.Body}
  +S = Bound.bd_st_stored(Bound.bd_fst.look(Bd.look(Bd.St{c, bs, nl, op, sd}, x)))
  +T = Bd.total(xs)
  +Lq = Bd.lines(1n+j, o)
  +R = Bound.bd_rev(xs)
  +Y = Bound.bd_rev(ys)
  +ML = Bd.margin.lines(Bd.mline(R, Lq), T)
  +S2 = Nat.sub(T, Nat.sub(T, Bd.least(mc, ML)))
  +eS = Equal.trans(Nat, S, Nat.sub(T, Nat.sub(T, Bd.margin(c, x))), S2, tk.stored(Bd.window(c, x), j, q0, bs, nl, op, x, T), Equal.cong(List<&2, Nat>, Nat, z => Nat.sub(T, Nat.sub(T, Bd.least(mc, Bd.margin.lines(Bd.mline(z, Lq), T)))), List.reverse(&2, Nat, xs), R, LBound.bnd.rev(xs)))
  +tT = Equal.trans(Nat, T, Bound.bd_total(xs), Bound.bd_total(R), LBound.bnd.total(xs), Equal.sym(Nat, Bound.bd_total(R), Bound.bd_total(xs), LBound.bnd.total_rev(xs)))
  +past2 = Equal.trans(Bool, Bool.or(Nat.is_lt(1n+q0, mc), Nat.is_le(T, mc)), Bool.or(Nat.is_lt(1n+q0, mc), Nat.is_le(Bound.bd_total(xs), mc)), True{}, Equal.cong(Nat, Bool, z => Bool.or(Nat.is_lt(1n+q0, mc), Nat.is_le(z, mc)), T, Bound.bd_total(xs), LBound.bnd.total(xs)), past)
  lgy = tk.fyl(Y, R, Lq, p, 1n+j, 1n+q0, tk.kq(j, o))
  cs = tk.case(j, q0, R, Y, p, w, T, mc, Bd.mline(R, Lq), tT, tk.lp_rev(xs, full), past2, lgy, Nat.is_le(mc, ML), {==})
  +H = Equal.trans(Bd.Win, Bd.keep(List.append(&2, Nat, Y, Bound.bd_glue(p, Bound.bd_rev(Bound.bd_kept(xs, S)))), 1n+j, 1n+q0, w), Bd.keep(List.append(&2, Nat, Y, Bound.bd_glue(p, Bound.bd_sfx(R, S))), 1n+j, 1n+q0, w), Bd.keep(List.append(&2, Nat, Y, Bound.bd_glue(p, R)), 1n+j, 1n+q0, w), Equal.cong(List<&2, Nat>, Bd.Win, z => Bd.keep(List.append(&2, Nat, Y, Bound.bd_glue(p, z)), 1n+j, 1n+q0, w), Bound.bd_rev(Bound.bd_kept(xs, S)), Bound.bd_sfx(R, S), tk.rev_kept(xs, S)), Equal.trans(Bd.Win, Bd.keep(List.append(&2, Nat, Y, Bound.bd_glue(p, Bound.bd_sfx(R, S))), 1n+j, 1n+q0, w), Bd.keep(List.append(&2, Nat, Y, Bound.bd_glue(p, Bound.bd_sfx(R, S2))), 1n+j, 1n+q0, w), Bd.keep(List.append(&2, Nat, Y, Bound.bd_glue(p, R)), 1n+j, 1n+q0, w), Equal.cong(Nat, Bd.Win, z => Bd.keep(List.append(&2, Nat, Y, Bound.bd_glue(p, Bound.bd_sfx(R, z))), 1n+j, 1n+q0, w), S, S2, eS), cs))
  tk.wineq(Bound.bd_kept(xs, S), xs, p, ys, j, q0, o2, h2, w, m2, H)

def Bound.bound_trim_keeps_later_windows(b, k, bs, nl, op, sd, xs, o, hc, tc, mc, p, ys, o2, h2, w, m2, full, past):
  match b:
    case 0n:
      match k:
        case 0n:
          {==}
        case 1n++j:
          {==}
    case 1n++q0:
      match k:
        case 0n:
          {==}
        case 1n++j:
          tk.main(j, q0, bs, nl, op, sd, xs, o, hc, tc, mc, p, ys, o2, h2, w, m2, full, past)
