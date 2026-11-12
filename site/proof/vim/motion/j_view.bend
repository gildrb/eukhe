# eukhe.com's Neovim: the proof of LAW j_view
# ===========================================
#
# On the editor after any events and an Esc (z = Idle.mk of it, cursor on
# line l, first line T in the band Final gives), j is Win.go_line to line
# m = min(l + 1, last), settled twice (Win.go, then Vim.fit). The first
# View.fit keeps T when the band of m still holds it and else moves it to
# hi(m) (JV.fit: lo only grows, hi grows by at most one, so a move is
# never more than half the window but in a window of at most two rows,
# where the middle is hi(m) too); the second keeps it (Esc.fit_back).

import Base
import ../../../vim/types.bend as T
import ../../../vim/buf.bend as B
import ../../../vim/move.bend as M
import ../../../vim/view.bend as V
import ../../../vim/st.bend as S
import ../../../vim/core.bend as C
import ../../../vim/vim.bend as Vim
import ../../../laws/vim/base.bend as Laws
import ../../../laws/vim/motion.bend as MotionLaws
import ../../base.bend as L
import ../../base/final.bend as Fi
import ../../base/reach.bend as Re
import ../screen/base.bend as Sb
import ../esc/base.bend as Eb
import ./base.bend as Mo
import ./col_base.bend as Cb

# Numbers
# -------

def JV.antisym(a: Nat, b: Nat, h1: L.LE(a, b), h2: L.LE(b, a)) -> {a == b : Nat}:
  match a b:
    case 0n 0n:
      {==}
    case 0n 1n+q:
      L.Bool.false_true({0n == 1n+q : Nat}, h2)
    case 1n+p 0n:
      L.Bool.false_true({1n+p == 0n : Nat}, h1)
    case 1n+p 1n+q:
      Equal.cong(Nat, Nat, x => 1n+x, p, q, JV.antisym(p, q, h1, h2))

# min is monotone on the right
def JV.min_mono_r(+a: Nat, +b: Nat, +c: Nat, h: L.LE(b, c)) -> L.LE(Nat.min(a, b), Nat.min(a, c)):
  L.Nat.le_min(Nat.min(a, b), a, c, L.Nat.min_le_l(a, b), L.Nat.le_trans(Nat.min(a, b), b, c, L.Nat.min_le_r(a, b), h))

# (1 + y) - d is at most 1 + (y - d)
def JV.sub_succ_le(y: Nat, d: Nat) -> L.LE(Nat.sub(1n+y, d), 1n+Nat.sub(y, d)):
  match y d:
    case 0n 0n:
      {==}
    case 1n+p 0n:
      L.Nat.le_refl(1n+1n+p)
    case 0n 1n+q:
      L.Nat.le_zero(1n+Nat.sub(0n, 1n+q))
    case 1n+p 1n+q:
      JV.sub_succ_le(p, q)

# y < x: not x <= y
def JV.lt_not_le(x: Nat, y: Nat, h: L.LT(y, x)) -> {Nat.is_le(x, y) == False{} : Bool}:
  match x y:
    case 0n 0n:
      L.Bool.false_true({Nat.is_le(0n, 0n) == False{} : Bool}, h)
    case 0n 1n+q:
      L.Bool.false_true({Nat.is_le(0n, 1n+q) == False{} : Bool}, h)
    case 1n+p 0n:
      {==}
    case 1n+p 1n+q:
      JV.lt_not_le(p, q, h)

# a <= y - z (a at least 1) gives a + z <= y
def JV.add_le(+a: Nat, z: Nat, y: Nat, h: L.LE(a, Nat.sub(y, z)), ha: L.LE(1n, a)) -> L.LE(Nat.add(a, z), y):
  match z y:
    case 0n _:
      %L.Nat.add_zero(a) : L.LE(_, y)
      %L.Nat.sub_zero(y) : L.LE(a, _)
      h
    case 1n+zp 0n:
      L.Bool.false_true(L.LE(Nat.add(a, 1n+zp), 0n), L.Nat.le_trans(1n, a, 0n, ha, h))
    case 1n+zp 1n+yp:
      %L.Nat.add_succ(a, zp) : L.LE(_, 1n+yp)
      JV.add_le(a, zp, yp, h, ha)

# t < x - d gives t + d < x
def JV.lt_add(+t: Nat, +d: Nat, +x: Nat, h: L.LT(t, Nat.sub(x, d))) -> L.LT(Nat.add(t, d), x):
  L.Nat.le_lt(Nat.add(t, d), x, JV.add_le(1n+t, d, x, L.Nat.lt_le(t, Nat.sub(x, d), h), L.Nat.le_add(1n, t)))

# the quotient divmod.go gives is at least the one it starts from
def JV.go_ge(+n: Nat, +m: Nat, +d: Nat, +r: Nat) -> L.LE(d, Pair.fst(Nat, Nat, Nat.divmod.go(n, m, d, r))):
  match n m:
    case 0n _:
      L.Nat.le_refl(d)
    case 1n+np 0n:
      L.Nat.le_trans(d, 1n+d, Pair.fst(Nat, Nat, Nat.divmod.go(np, r, 1n+d, 0n)), L.Nat.le_succ(d, d, L.Nat.le_refl(d)), JV.go_ge(np, r, 1n+d, 0n))
    case 1n+np 1n+mp:
      JV.go_ge(np, mp, d, 1n+r)

# a window whose half (less one) is 0 has at most two rows
def JV.small(+h: Nat, e: L.LT(Nat.div(Nat.sub(h, 1n), 2n), 1n)) -> L.LE(h, 2n):
  match h:
    case 0n:
      {==}
    case 1n+a:
      match a:
        case 0n:
          {==}
        case 1n+b:
          match b:
            case 0n:
              {==}
            case 1n+k:
              L.Nat.le_lt_absurd(L.LE(1n+1n+1n+k, 2n), 1n, Pair.fst(Nat, Nat, Nat.divmod.go(k, 1n, 1n, 0n)), JV.go_ge(k, 1n, 1n, 0n), e)

# Bands
# -----

# hi of the next line is at most one more
def JV.hi_succ(+l: Nat, +sd: Nat, +last: Nat, +h: Nat) -> L.LE(Fi.Fin.hi(1n+l, sd, last, h), 1n+Fi.Fin.hi(l, sd, last, h)):
  +d = Nat.sub(h, 1n)
  +x = Nat.add(l, Nat.min(sd, Nat.sub(last, 1n+l)))
  +y = Nat.add(l, Nat.min(sd, Nat.sub(last, l)))
  +hxy = L.Nat.le_add_mono(l, Nat.min(sd, Nat.sub(last, 1n+l)), Nat.min(sd, Nat.sub(last, l)), JV.min_mono_r(sd, Nat.sub(last, 1n+l), Nat.sub(last, l), L.Nat.sub_anti(last, l, 1n+l, L.Nat.le_succ(l, l, L.Nat.le_refl(l)))))
  L.Nat.le_trans(Nat.sub(1n+x, d), Nat.sub(1n+y, d), 1n+Nat.sub(y, d), L.Nat.sub_mono(1n+x, 1n+y, d, hxy), JV.sub_succ_le(y, d))

def JV.hi_step.go(+l: Nat, +sd: Nat, +last: Nat, +h: Nat, b: Bool, e: {Nat.is_le(1n+l, last) == b : Bool}, hl: L.LE(l, last))
  -> L.LE(Fi.Fin.hi(Nat.min(1n+l, last), sd, last, h), 1n+Fi.Fin.hi(l, sd, last, h)):
  match b:
    case True{}:
      %Equal.sym(Nat, Nat.min(1n+l, last), 1n+l, Mo.Min.eq_l(1n+l, last, e)) : L.LE(Fi.Fin.hi(_, sd, last, h), 1n+Fi.Fin.hi(l, sd, last, h))
      JV.hi_succ(l, sd, last, h)
    case False{}:
      +hle = L.Nat.lt_le(last, 1n+l, L.Nat.not_le(1n+l, last, e))
      %Equal.sym(Nat, Nat.min(1n+l, last), last, L.Nat.min_eq_r(1n+l, last, L.Nat.le_succ(last, l, hle))) : L.LE(Fi.Fin.hi(_, sd, last, h), 1n+Fi.Fin.hi(l, sd, last, h))
      %Equal.sym(Nat, last, l, JV.antisym(last, l, hle, hl)) : L.LE(Fi.Fin.hi(_, sd, last, h), 1n+Fi.Fin.hi(l, sd, last, h))
      L.Nat.le_succ(Fi.Fin.hi(l, sd, last, h), Fi.Fin.hi(l, sd, last, h), L.Nat.le_refl(Fi.Fin.hi(l, sd, last, h)))

# the line j goes to, min(l + 1, last): hi there is at most hi(l) + 1
def JV.hi_step(+l: Nat, +sd: Nat, +last: Nat, +h: Nat, hl: L.LE(l, last)) -> L.LE(Fi.Fin.hi(Nat.min(1n+l, last), sd, last, h), 1n+Fi.Fin.hi(l, sd, last, h)):
  JV.hi_step.go(l, sd, last, h, Nat.is_le(1n+l, last), {==}, hl)

# in a window of two rows the middle is at most hi
def JV.two(+m: Nat, +last: Nat, c: Bool, e: {Nat.is_lt(m, last) == c : Bool}, hm: L.LE(m, last))
  -> L.LE(Nat.min(Nat.sub(m, 0n), Nat.sub(last, Nat.min(last, 1n))), Nat.sub(Nat.add(m, Nat.min(1n, Nat.sub(last, m))), 1n)):
  match c:
    case True{}:
      +z = Nat.sub(last, Nat.min(last, 1n))
      +ge1 = L.Nat.lt_le(0n, Nat.sub(last, m), L.Nat.sub_pos(m, last, e))
      %Equal.sym(Nat, Nat.min(1n, Nat.sub(last, m)), 1n, Mo.Min.eq_l(1n, Nat.sub(last, m), ge1)) : L.LE(Nat.min(Nat.sub(m, 0n), z), Nat.sub(Nat.add(m, _), 1n))
      %Equal.sym(Nat, Nat.add(m, 1n), 1n+m, Mo.Plus1(m)) : L.LE(Nat.min(Nat.sub(m, 0n), z), Nat.sub(_, 1n))
      L.Nat.min_le_l(Nat.sub(m, 0n), z)
    case False{}:
      +hlm = L.Nat.not_lt(m, last, e)
      +k = Nat.min(1n, Nat.sub(last, m))
      +hz = L.Nat.le_trans(Nat.sub(last, 1n), Nat.sub(m, 1n), Nat.sub(Nat.add(m, k), 1n), L.Nat.sub_mono(last, m, 1n, hlm), L.Nat.sub_mono(m, Nat.add(m, k), 1n, L.Nat.le_add(m, k)))
      %L.Nat.sub_min(last, 1n) : L.LE(Nat.min(Nat.sub(m, 0n), _), Nat.sub(Nat.add(m, k), 1n))
      L.Nat.le_trans(Nat.min(Nat.sub(m, 0n), Nat.sub(last, 1n)), Nat.sub(last, 1n), Nat.sub(Nat.add(m, k), 1n), L.Nat.min_le_r(Nat.sub(m, 0n), Nat.sub(last, 1n)), hz)

# in a window of at most two rows the middle View.fit picks is at most hi
def JV.mid_small(h: Nat, +m: Nat, +last: Nat, hm: L.LE(m, last), hh: L.LE(h, 2n))
  -> L.LE(Nat.min(Nat.sub(m, Nat.div(Nat.sub(h, 1n), 2n)), Nat.sub(last, Nat.min(last, Nat.sub(h, 1n)))), Fi.Fin.hi(m, V.View.so_dn(h), last, h)):
  match h:
    case 0n:
      L.Nat.le_trans(Nat.min(Nat.sub(m, 0n), Nat.sub(last, Nat.min(last, 0n))), Nat.sub(m, 0n), Nat.sub(Nat.add(m, 0n), 0n), L.Nat.min_le_l(Nat.sub(m, 0n), Nat.sub(last, Nat.min(last, 0n))), L.Nat.sub_mono(m, Nat.add(m, 0n), 0n, L.Nat.le_add(m, 0n)))
    case 1n+a:
      match a:
        case 0n:
          L.Nat.le_trans(Nat.min(Nat.sub(m, 0n), Nat.sub(last, Nat.min(last, 0n))), Nat.sub(m, 0n), Nat.sub(Nat.add(m, 0n), 0n), L.Nat.min_le_l(Nat.sub(m, 0n), Nat.sub(last, Nat.min(last, 0n))), L.Nat.sub_mono(m, Nat.add(m, 0n), 0n, L.Nat.le_add(m, 0n)))
        case 1n+b:
          match b:
            case 0n:
              JV.two(m, last, Nat.is_lt(m, last), {==}, hm)
            case 1n+k:
              L.Bool.false_true(L.LE(Nat.min(Nat.sub(m, Nat.div(Nat.sub(1n+1n+1n+k, 1n), 2n)), Nat.sub(last, Nat.min(last, Nat.sub(1n+1n+1n+k, 1n)))), Fi.Fin.hi(m, V.View.so_dn(1n+1n+1n+k), last, 1n+1n+1n+k)), hh)

# View.fit's choice when lo does not move it
def JV.pick2(c1: Bool, c2: Bool, -up: Nat, -down: Nat, -t: Nat, -r: Nat, e1: {c1 == False{} : Bool}, kt: {c2 == False{} : Bool} -> {t == r : Nat}, kd: {c2 == True{} : Bool} -> {down == r : Nat})
  -> {Bool.pick(Nat, c1, up, Bool.pick(Nat, c2, down, t)) == r : Nat}:
  match c1 c2:
    case True{} True{}:
      L.Bool.true_false({Bool.pick(Nat, True{}, up, Bool.pick(Nat, True{}, down, t)) == r : Nat}, e1)
    case True{} False{}:
      L.Bool.true_false({Bool.pick(Nat, True{}, up, Bool.pick(Nat, False{}, down, t)) == r : Nat}, e1)
    case False{} True{}:
      kd({==})
    case False{} False{}:
      kt({==})

def JV.pick1(c: Bool, -mid: Nat, -hi: Nat, k: {c == True{} : Bool} -> {mid == hi : Nat}) -> {Bool.pick(Nat, c, mid, hi) == hi : Nat}:
  match c:
    case True{}:
      k({==})
    case False{}:
      {==}

def JV.band_hi(-t: Nat, -lo: Nat, -hi: Nat, b: Fi.Band(t, lo, hi)) -> L.LE(hi, t):
  match b:
    case (bh, bl):
      bh

# hi(m) not past t: View.fit stays, and t is what the claim asks
def JV.stay(+need: Nat, +d: Nat, +t: Nat, e: {Nat.is_gt(Nat.sub(need, d), t) == False{} : Bool}) -> {t == Bool.pick(Nat, Nat.is_le(need, Nat.add(t, d)), t, Nat.sub(need, d)) : Nat}:
  +hle = L.Nat.sub_le_add(need, d, t, L.Nat.not_gt(Nat.sub(need, d), t, e))
  %Equal.sym(Bool, Nat.is_le(need, Nat.add(t, d)), True{}, hle) : {t == Bool.pick(Nat, _, t, Nat.sub(need, d)) : Nat}
  {==}

# a move of more than half the window, by one line at most: the window
# has at most two rows, and the middle is hi(m)
def JV.mid_eq(+t: Nat, +m: Nat, +h: Nat, +last: Nat, e: {Nat.is_gt(Nat.sub(Fi.Fin.hi(m, V.View.so_dn(h), last, h), t), Nat.div(Nat.sub(h, 1n), 2n)) == True{} : Bool}, hstep: L.LE(Fi.Fin.hi(m, V.View.so_dn(h), last, h), 1n+t), +hm: L.LE(m, last))
  -> {Nat.min(Nat.sub(m, Nat.div(Nat.sub(h, 1n), 2n)), Nat.sub(last, Nat.min(last, Nat.sub(h, 1n)))) == Fi.Fin.hi(m, V.View.so_dn(h), last, h) : Nat}:
  +half = Nat.div(Nat.sub(h, 1n), 2n)
  +hi = Fi.Fin.hi(m, V.View.so_dn(h), last, h)
  +mid = Nat.min(Nat.sub(m, half), Nat.sub(last, Nat.min(last, Nat.sub(h, 1n))))
  +hlt = L.Nat.gt_lt(Nat.sub(hi, t), half, e)
  +hle1 = L.Nat.le_add_sub(hi, t, 1n, hstep)
  +h1 = L.Nat.le_lt(half, 1n, L.Nat.le_trans(1n+half, Nat.sub(hi, t), 1n, L.Nat.lt_le(half, Nat.sub(hi, t), hlt), hle1))
  +band = Fi.Fit.mid(m, h, last, V.View.so_in(h), V.View.so_dn(h), half, hm, Fi.Fit.so_half(h), Fi.Fit.half_dn(h))
  JV.antisym(mid, hi, JV.mid_small(h, m, last, hm, JV.small(h, h1)), JV.band_hi(mid, Fi.Fin.lo(m, V.View.so_in(h)), hi, band))

# hi(m) past t: View.fit moves down to hi(m), as the claim asks
def JV.move(+t: Nat, +m: Nat, +h: Nat, +last: Nat, e: {Nat.is_gt(Fi.Fin.hi(m, V.View.so_dn(h), last, h), t) == True{} : Bool}, +hstep: L.LE(Fi.Fin.hi(m, V.View.so_dn(h), last, h), 1n+t), +hm: L.LE(m, last))
  -> {Bool.pick(Nat, Nat.is_gt(Nat.sub(Fi.Fin.hi(m, V.View.so_dn(h), last, h), t), Nat.div(Nat.sub(h, 1n), 2n)), Nat.min(Nat.sub(m, Nat.div(Nat.sub(h, 1n), 2n)), Nat.sub(last, Nat.min(last, Nat.sub(h, 1n)))), Fi.Fin.hi(m, V.View.so_dn(h), last, h))
    == Bool.pick(Nat, Nat.is_le(Nat.add(m, Nat.min(V.View.so_dn(h), Nat.sub(last, m))), Nat.add(t, Nat.sub(h, 1n))), t, Fi.Fin.hi(m, V.View.so_dn(h), last, h)) : Nat}:
  +d = Nat.sub(h, 1n)
  +half = Nat.div(d, 2n)
  +need = Nat.add(m, Nat.min(V.View.so_dn(h), Nat.sub(last, m)))
  +hi = Fi.Fin.hi(m, V.View.so_dn(h), last, h)
  +mid = Nat.min(Nat.sub(m, half), Nat.sub(last, Nat.min(last, d)))
  +nle = JV.lt_not_le(need, Nat.add(t, d), JV.lt_add(t, d, need, L.Nat.gt_lt(hi, t, e)))
  %Equal.sym(Bool, Nat.is_le(need, Nat.add(t, d)), False{}, nle) : {Bool.pick(Nat, Nat.is_gt(Nat.sub(hi, t), half), mid, hi) == Bool.pick(Nat, _, t, hi) : Nat}
  JV.pick1(Nat.is_gt(Nat.sub(hi, t), half), mid, hi, e2 => JV.mid_eq(t, m, h, last, e2, hstep, hm))

# View.fit from first line T, in the band of line l, to line m (l <= m,
# hi(m) at most T + 1): T when m's band holds it, else hi(m)
def JV.fit(+t: Nat, +l: Nat, +m: Nat, +h: Nat, +last: Nat, bh: L.LE(Fi.Fin.hi(l, V.View.so_dn(h), last, h), t), bl: L.LE(t, Fi.Fin.lo(l, V.View.so_in(h))), hlm: L.LE(l, m), +hstep: L.LE(Fi.Fin.hi(m, V.View.so_dn(h), last, h), 1n+t), +hm: L.LE(m, last))
  -> {V.View.fit(t, m, h, last) == Bool.pick(Nat, Nat.is_le(Nat.add(m, Nat.min(V.View.so_dn(h), Nat.sub(last, m))), Nat.add(t, Nat.sub(h, 1n))), t, Fi.Fin.hi(m, V.View.so_dn(h), last, h)) : Nat}:
  +so = V.View.so_in(h)
  +sd = V.View.so_dn(h)
  +half = Nat.div(Nat.sub(h, 1n), 2n)
  +d = Nat.sub(h, 1n)
  +lo = Nat.sub(m, Nat.min(so, m))
  +need = Nat.add(m, Nat.min(sd, Nat.sub(last, m)))
  +hi = Nat.sub(need, d)
  +mid = Nat.min(Nat.sub(m, half), Nat.sub(last, Nat.min(last, d)))
  +up = Bool.pick(Nat, Nat.is_gt(Nat.sub(t, lo), half), mid, lo)
  +down = Bool.pick(Nat, Nat.is_gt(Nat.sub(hi, t), half), mid, hi)
  +r = Bool.pick(Nat, Nat.is_le(need, Nat.add(t, d)), t, hi)
  +blo = L.Nat.le_trans(t, Fi.Fin.lo(l, so), lo, bl, Eb.Esc.lo_mono(so, l, m, hlm))
  JV.pick2(Nat.is_lt(lo, t), Nat.is_gt(hi, t), up, down, t, r, L.Nat.le_not_lt(lo, t, blo),
    e => JV.stay(need, d, t, e),
    e => JV.move(t, m, h, last, e, hstep, hm))

# The editor
# ----------

# the first line Win.go_line's two settles give (Win.go, then Vim.fit)
def JV.DF(+z: T.St, +l: Nat) -> Nat:
  +ls = C.St.lines(z)
  +last = M.Move.last_line(ls)
  +m = Nat.min(l, last)
  +p = {T.Pos{m, M.Move.aim(ls, m, S.Win.want(S.St.win(z)))} : T.Pos}
  +h1 = C.St.h(z)
  +h2 = V.View.text_rows(Nat.max(S.St.rows(z), V.View.min_rows()))
  V.View.fit(Nat.min(V.View.fit(Nat.min(S.Win.top(S.St.win(z)), V.View.max_top(h1, last)), S.Pos.line(Mo.Cl2(ls, p)), h1, last), V.View.max_top(h2, last)), S.Pos.line(Mo.Cl3(ls, p)), h2, last)

def JV.top(+z: T.St, +l: Nat) -> {S.Win.top(S.St.win(Vim.Vim.fit(Vim.Vim.keep(z, C.Win.go_line(z, l))))) == JV.DF(z, l) : Nat}:
  match z:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              {==}
            case T.Dir{+path}:
              {==}

# the frame's first line is the window's
def JV.ftop(+x: T.St) -> {Laws.F.top(Vim.Vim.frame(x)) == S.Win.top(S.St.win(x)) : Nat}:
  {==}

# what Claim.j_view tests, of the first lines before (ta) and after (tb),
# the line need must show and the text rows h
def JV.Q(+tb: Nat, +ta: Nat, +need: Nat, +h: Nat) -> Bool:
  Nat.is_eq(tb, Bool.pick(Nat, Nat.is_le(need, Nat.add(ta, Nat.sub(h, 1n))), ta, Nat.sub(need, Nat.sub(h, 1n))))

# hi of the line j goes to is at most the first line + 1
def JV.hstep(+ln: Nat, +sd: Nat, +last: Nat, +h: Nat, +top: Nat, fl: L.LE(ln, last), bh: L.LE(Fi.Fin.hi(ln, sd, last, h), top)) -> L.LE(Fi.Fin.hi(Nat.min(Nat.add(ln, 1n), last), sd, last, h), 1n+top):
  %Equal.sym(Nat, Nat.add(ln, 1n), 1n+ln, Mo.Plus1(ln)) : L.LE(Fi.Fin.hi(Nat.min(_, last), sd, last, h), 1n+top)
  L.Nat.le_trans(Fi.Fin.hi(Nat.min(1n+ln, last), sd, last, h), 1n+Fi.Fin.hi(ln, sd, last, h), 1n+top, JV.hi_step(ln, sd, last, h, fl), bh)

# the two settles: the first fits top to line m (JV.fit), the second
# keeps it (Esc.fit_back), both on rows >= 3
def JV.collapse(+top: Nat, +ln: Nat, +m: Nat, +rows: Nat, +last: Nat, +a1: Nat, +a2: Nat, e1: {a1 == m : Nat}, e2: {a2 == m : Nat}, f3: L.LE(3n, rows),
  bh: L.LE(Fi.Fin.hi(ln, V.View.so_dn(V.View.text_rows(rows)), last, V.View.text_rows(rows)), top), +bl: L.LE(top, Fi.Fin.lo(ln, V.View.so_in(V.View.text_rows(rows)))),
  +fl: L.LE(ln, last), hlm: L.LE(ln, m), hstep: L.LE(Fi.Fin.hi(m, V.View.so_dn(V.View.text_rows(rows)), last, V.View.text_rows(rows)), 1n+top), +hm: L.LE(m, last))
  -> {V.View.fit(Nat.min(V.View.fit(Nat.min(top, V.View.max_top(V.View.text_rows(rows), last)), a1, V.View.text_rows(rows), last), V.View.max_top(V.View.text_rows(Nat.max(rows, V.View.min_rows())), last)), a2, V.View.text_rows(Nat.max(rows, V.View.min_rows())), last)
    == Bool.pick(Nat, Nat.is_le(Nat.add(m, Nat.min(V.View.so_dn(V.View.text_rows(rows)), Nat.sub(last, m))), Nat.add(top, Nat.sub(V.View.text_rows(rows), 1n))), top, Fi.Fin.hi(m, V.View.so_dn(V.View.text_rows(rows)), last, V.View.text_rows(rows))) : Nat}:
  +h = V.View.text_rows(rows)
  +so = V.View.so_in(h)
  +mt = V.View.max_top(h, last)
  +r = Bool.pick(Nat, Nat.is_le(Nat.add(m, Nat.min(V.View.so_dn(h), Nat.sub(last, m))), Nat.add(top, Nat.sub(h, 1n))), top, Fi.Fin.hi(m, V.View.so_dn(h), last, h))
  +f1 = V.View.fit(top, m, h, last)
  +band1 = Fi.Fit.band(top, m, h, last, hm)
  %Eb.Esc.max_back(rows, 3n, f3) : {V.View.fit(Nat.min(V.View.fit(Nat.min(top, mt), a1, h, last), V.View.max_top(V.View.text_rows(_), last)), a2, V.View.text_rows(_), last) == r : Nat}
  %Equal.sym(Nat, a1, m, e1) : {V.View.fit(Nat.min(V.View.fit(Nat.min(top, mt), _, h, last), mt), a2, h, last) == r : Nat}
  %Equal.sym(Nat, a2, m, e2) : {V.View.fit(Nat.min(V.View.fit(Nat.min(top, mt), m, h, last), mt), _, h, last) == r : Nat}
  %Eb.Esc.min_back(top, mt, L.Nat.le_trans(top, Fi.Fin.lo(ln, so), mt, bl, Eb.Esc.lo_mono(so, ln, last, fl))) : {V.View.fit(Nat.min(V.View.fit(_, m, h, last), mt), m, h, last) == r : Nat}
  %Eb.Esc.min_back(f1, mt, L.Nat.le_trans(f1, Fi.Fin.lo(m, so), mt, Eb.Esc.band_lo(f1, Fi.Fin.lo(m, so), Fi.Fin.hi(m, V.View.so_dn(h), last, h), band1), Eb.Esc.lo_mono(so, m, last, hm))) : {V.View.fit(_, m, h, last) == r : Nat}
  %Eb.Esc.fit_back(f1, m, h, last, band1) : {_ == r : Nat}
  JV.fit(top, ln, m, h, last, bh, bl, hlm, hstep, hm)

# j from the settled editor z = Idle.mk(s): the first line after it
def JV.core(+fs: List<&2, T.Buf>, +s: T.St, hf: {S.St.files(s) == B.Files.some(fs, Nil{}) : List<&2, T.Buf>}, hr: {B.Tgt.real(S.St.files(s), S.Win.tgt(S.St.win(s))) == True{} : Bool}, +fin: Fi.Final(Mo.Idle.mk(s)))
  -> {Laws.Claim.j_view(fs, Mo.Idle.mk(s), S.St.rows(s)) == True{} : Bool}:
  (f3, r1) = fin
  (f12, r2) = r1
  (fl, r3) = r2
  (fc, r4) = r3
  (bt, bs) = r4
  (bh, bl) = bt
  +z = Mo.Idle.mk(s)
  +rows = S.St.rows(s)
  +h = V.View.text_rows(rows)
  +so = V.View.so_in(h)
  +sd = V.View.so_dn(h)
  +d = Nat.sub(h, 1n)
  +ls = C.St.lines(z)
  +last = M.Move.last_line(ls)
  +top = S.Win.top(S.St.win(z))
  +ln = C.St.line(z)
  +l = Nat.add(ln, 1n)
  +m = Nat.min(l, last)
  +w = S.Win.want(S.St.win(z))
  +p = {T.Pos{m, M.Move.aim(ls, m, w)} : T.Pos}
  +st = C.Win.go_line(z, l)
  +y = Vim.Vim.keep(z, st)
  +t = Vim.Vim.fit(y)
  +need = Nat.add(m, Nat.min(sd, Nat.sub(last, m)))
  +r = Bool.pick(Nat, Nat.is_le(need, Nat.add(top, d)), top, Nat.sub(need, d))
  +mt = V.View.max_top(h, last)
  +hm = L.Nat.min_le_r(l, last)
  +hlm = L.Nat.le_min(ln, l, last, L.Nat.le_add(ln, 1n), fl)
  +cl = Mo.Clamp.on(ls, m, M.Move.aim(ls, m, w), hm, Mo.Aim.le(ls, m, w))
  +e1 = Equal.cong(T.Pos, Nat, q => S.Pos.line(q), Mo.Cl2(ls, p), p, Mo.Cl2.on(ls, p, cl))
  +e3 = Mo.Cl3.on(ls, p, cl)
  +e2 = Equal.cong(T.Pos, Nat, q => S.Pos.line(q), Mo.Cl3(ls, p), p, e3)
  +hstep = JV.hstep(ln, sd, last, h, top, fl, bh)
  +ecol = JV.collapse(top, ln, m, rows, last, S.Pos.line(Mo.Cl2(ls, p)), S.Pos.line(Mo.Cl3(ls, p)), e1, e2, f3, bh, bl, fl, hlm, hstep, hm)
  +etop = Equal.trans(Nat, Laws.F.top(Vim.Vim.frame(t)), S.Win.top(S.St.win(t)), r, JV.ftop(t), Equal.trans(Nat, S.Win.top(S.St.win(t)), JV.DF(z, l), r, JV.top(z, l), ecol))
  +ecur = Equal.trans(T.Pos, S.Win.cur(S.St.win(t)), Mo.Cl3(ls, p), p, Mo.GL.cur(z, l), e3)
  +em = Equal.trans(Nat, Laws.Spec.at_line(Vim.Vim.frame(t)), C.St.line(t), m, Mo.AtLine(t, Fi.Final.of_fit(y)), Equal.cong(T.Pos, Nat, q => S.Pos.line(q), S.Win.cur(S.St.win(t)), p, ecur))
  +H = Nat.sub(rows, 2n)
  +spl = Laws.Spec.lines(fs, z)
  +so8 = Laws.Spec.min(8n, Nat.div(H, 2n))
  %Equal.sym(T.St, Laws.Spec.press(z, "j"), t, Cb.VCol.press(z, "j", st, {==}, hr, {==})) : {JV.Q(Laws.F.top(Vim.Vim.frame(_)), Laws.F.top(Vim.Vim.frame(z)), Nat.add(Laws.Spec.at_line(Vim.Vim.frame(_)), Laws.Spec.min(so8, Nat.sub(Laws.Spec.last(Laws.Spec.count(spl)), Laws.Spec.at_line(Vim.Vim.frame(_))))), H) == True{} : Bool}
  %Equal.sym(Nat, Laws.F.top(Vim.Vim.frame(t)), r, etop) : {JV.Q(_, Laws.F.top(Vim.Vim.frame(z)), Nat.add(Laws.Spec.at_line(Vim.Vim.frame(t)), Laws.Spec.min(so8, Nat.sub(Laws.Spec.last(Laws.Spec.count(spl)), Laws.Spec.at_line(Vim.Vim.frame(t))))), H) == True{} : Bool}
  %Equal.sym(Nat, Laws.F.top(Vim.Vim.frame(z)), top, JV.ftop(z)) : {JV.Q(r, _, Nat.add(Laws.Spec.at_line(Vim.Vim.frame(t)), Laws.Spec.min(so8, Nat.sub(Laws.Spec.last(Laws.Spec.count(spl)), Laws.Spec.at_line(Vim.Vim.frame(t))))), H) == True{} : Bool}
  %Equal.sym(Nat, Laws.Spec.at_line(Vim.Vim.frame(t)), m, em) : {JV.Q(r, top, Nat.add(_, Laws.Spec.min(so8, Nat.sub(Laws.Spec.last(Laws.Spec.count(spl)), _))), H) == True{} : Bool}
  %Equal.sym(List<&2, String>, spl, ls, Mo.Lines.spec(fs, z, hf)) : {JV.Q(r, top, Nat.add(m, Laws.Spec.min(so8, Nat.sub(Laws.Spec.last(Laws.Spec.count(_)), m))), H) == True{} : Bool}
  %Equal.sym(Nat, Laws.Spec.last(Laws.Spec.count(ls)), last, Mo.LastLine.eq(ls)) : {JV.Q(r, top, Nat.add(m, Laws.Spec.min(so8, Nat.sub(_, m))), H) == True{} : Bool}
  %Equal.sym(Nat, so8, sd, Sb.Spec.min_eq(8n, Nat.div(H, 2n))) : {JV.Q(r, top, Nat.add(m, Laws.Spec.min(_, Nat.sub(last, m))), H) == True{} : Bool}
  %Equal.sym(Nat, Laws.Spec.min(sd, Nat.sub(last, m)), Nat.min(sd, Nat.sub(last, m)), Sb.Spec.min_eq(sd, Nat.sub(last, m))) : {JV.Q(r, top, Nat.add(m, _), H) == True{} : Bool}
  L.Nat.eq_refl(r)

def JV.law(+fs: List<&2, T.Buf>, +rows: Nat, +cols: Nat, +evs: List<&2, T.Ev>) -> {Laws.Claim.j_view(fs, Laws.Spec.normal(fs, rows, cols, evs), Laws.Spec.rows(rows, evs)) == True{} : Bool}:
  +n = Laws.Spec.normal(fs, rows, cols, evs)
  %Re.Reach.rows_normal(fs, rows, cols, evs) : {Laws.Claim.j_view(fs, n, _) == True{} : Bool}
  %Equal.sym(T.St, n, Mo.Idle.mk(n), Mo.Ready.eta(fs, rows, cols, evs)) : {Laws.Claim.j_view(fs, _, S.St.rows(n)) == True{} : Bool}
  JV.core(fs, n, Mo.Ready.files(fs, rows, cols, evs), Mo.Ready.real(fs, rows, cols, evs), Mo.Ready.fin(fs, rows, cols, evs))

def MotionLaws.j_view(fs, rows, cols, evs):
  JV.law(fs, rows, cols, evs)
