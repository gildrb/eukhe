# eukhe.com's Neovim: the settled editor
# ======================================
#
# Vim.final (vim/vim.bend) ends Vim.init and every Vim.step. What it gives
# every editor, whatever came before: a screen of at least 3 x 12, the
# cursor on a line and a character of the window's lines, and the window
# scrolled so that 'scrolloff' holds both ways (Band). Final(s) names
# these facts; Final.of proves them for Vim.final(x), for every x.

import Base
import ../../vim/types.bend as T
import ../../vim/buf.bend as B
import ../../vim/move.bend as M
import ../../vim/view.bend as V
import ../../vim/st.bend as S
import ../../vim/core.bend as C
import ../../vim/vim.bend as Vim
import ../base.bend as L

# Bands
# -----

# the first line the window may take with the cursor on line l
# ('scrolloff' so above it)
def Fin.lo(+l: Nat, +so: Nat) -> Nat:
  Nat.sub(l, Nat.min(so, l))

# the least first line with 'scrolloff' so below line l, in a window of h
# rows over lines up to last
def Fin.hi(+l: Nat, +so: Nat, +last: Nat, +h: Nat) -> Nat:
  Nat.sub(Nat.add(l, Nat.min(so, Nat.sub(last, l))), Nat.sub(h, 1n))

# t between hi and lo
def Band(t: Nat, lo: Nat, hi: Nat) -> Data:
  Sigma<&2, &2, L.LE(hi, t), _ => L.LE(t, lo)>

def Band.pick(c: Bool, -x: Nat, -y: Nat, -lo: Nat, -hi: Nat, bx: Band(x, lo, hi), by: Band(y, lo, hi)) -> Band(Bool.pick(Nat, c, x, y), lo, hi):
  match c:
    case True{}:
      bx
    case False{}:
      by

# View.fit's and View.fit_side's choice: up when lo < top, down when
# hi > top, else top
def Band.pick2(c1: Bool, c2: Bool, +lo: Nat, +hi: Nat, +top: Nat, -up: Nat, -down: Nat, e1: {Nat.is_lt(lo, top) == c1 : Bool}, e2: {Nat.is_gt(hi, top) == c2 : Bool}, bu: Band(up, lo, hi), bd: Band(down, lo, hi))
  -> Band(Bool.pick(Nat, c1, up, Bool.pick(Nat, c2, down, top)), lo, hi):
  match c1 c2:
    case True{} _:
      bu
    case False{} True{}:
      bd
    case False{} False{}:
      (L.Nat.not_gt(hi, top, e2), L.Nat.not_lt(lo, top, e1))

# hi is at most l - x when x + a fits the window (a: the scrolloff below)
def Fit.hi_le(+l: Nat, +a: Nat, +x: Nat, +h: Nat, hx: L.LE(Nat.add(x, a), Nat.sub(h, 1n))) -> L.LE(Nat.sub(Nat.add(l, a), Nat.sub(h, 1n)), Nat.sub(l, x)):
  L.LE.cast_r(Nat.sub(Nat.add(l, a), Nat.sub(h, 1n)), Nat.sub(Nat.add(l, a), Nat.add(x, a)), Nat.sub(l, x), L.Nat.sub_cancel_r(l, x, a), L.Nat.sub_anti(Nat.add(l, a), Nat.add(x, a), Nat.sub(h, 1n), hx))

# the bands a window of h rows keeps: scrolloff so above the cursor (at
# most half of its rows less one), sd below, half + sd at most h - 1
def Fit.hilo(+l: Nat, +h: Nat, +last: Nat, +so: Nat, +sd: Nat, +half: Nat, +h1: L.LE(so, half), h2: L.LE(Nat.add(half, sd), Nat.sub(h, 1n)))
  -> L.LE(Fin.hi(l, sd, last, h), Fin.lo(l, so)):
  +a = Nat.min(sd, Nat.sub(last, l))
  +b = Nat.min(so, l)
  +ha = L.Nat.min_le_l(sd, Nat.sub(last, l))
  +hb = L.Nat.min_le_l(so, l)
  Fit.hi_le(l, a, b, h, L.Nat.le_trans(Nat.add(b, a), Nat.add(half, sd), Nat.sub(h, 1n), L.Nat.le_add2(b, half, a, sd, L.Nat.le_trans(b, so, half, hb, h1), ha), h2))

def Fit.mid(+l: Nat, +h: Nat, +last: Nat, +so: Nat, +sd: Nat, +half: Nat, hl: L.LE(l, last), +h1: L.LE(so, half), h2: L.LE(Nat.add(half, sd), Nat.sub(h, 1n)))
  -> Band(Nat.min(Nat.sub(l, half), Nat.sub(last, Nat.min(last, Nat.sub(h, 1n)))), Fin.lo(l, so), Fin.hi(l, sd, last, h)):
  +a = Nat.min(sd, Nat.sub(last, l))
  +b = Nat.min(so, l)
  +lo = Fin.lo(l, so)
  +hi = Fin.hi(l, sd, last, h)
  +mid = Nat.min(Nat.sub(l, half), Nat.sub(last, Nat.min(last, Nat.sub(h, 1n))))
  +ha = L.Nat.min_le_l(sd, Nat.sub(last, l))
  +hb = L.Nat.min_le_l(so, l)
  +m1 = Fit.hi_le(l, a, half, h, L.Nat.le_trans(Nat.add(half, a), Nat.add(half, sd), Nat.sub(h, 1n), L.Nat.le_add_mono(half, a, sd, ha), h2))
  +la = L.LE.cast_r(Nat.add(l, a), Nat.add(l, Nat.sub(last, l)), last, L.Nat.add_sub(last, l, hl), L.Nat.le_add_mono(l, a, Nat.sub(last, l), L.Nat.min_le_r(sd, Nat.sub(last, l))))
  +m2 = L.LE.cast_r(hi, Nat.sub(last, Nat.sub(h, 1n)), Nat.sub(last, Nat.min(last, Nat.sub(h, 1n))), L.Nat.sub_min(last, Nat.sub(h, 1n)), L.Nat.sub_mono(Nat.add(l, a), last, Nat.sub(h, 1n), la))
  +midlo = L.Nat.le_trans(mid, Nat.sub(l, half), lo, L.Nat.min_le_l(Nat.sub(l, half), Nat.sub(last, Nat.min(last, Nat.sub(h, 1n)))), L.Nat.sub_anti(l, b, half, L.Nat.le_trans(b, so, half, hb, h1)))
  (L.Nat.le_min(hi, Nat.sub(l, half), Nat.sub(last, Nat.min(last, Nat.sub(h, 1n))), m1, m2), midlo)

# the scrolloff of a window of h rows is at most half of its rows less one
def Fit.so_half(+h: Nat) -> L.LE(V.View.so_in(h), Nat.div(Nat.sub(h, 1n), 2n)):
  L.Nat.min_le_r(V.View.so(), Nat.div(Nat.sub(h, 1n), 2n))

# the scrolloff above is at most the one below
def Fit.so_le_dn(h: Nat) -> L.LE(V.View.so_in(h), V.View.so_dn(h)):
  match h:
    case 0n:
      {==}
    case 1n++n:
      +d1 = Nat.div(Nat.sub(n, 0n), 2n)
      +d2 = Nat.div(1n+n, 2n)
      +e = Equal.cong(Nat, Nat, z => Nat.div(z, 2n), Nat.sub(n, 0n), n, L.Nat.sub_zero(n))
      +m = L.LE.cast_l(Nat.div(n, 2n), d1, d2, Equal.sym(Nat, d1, Nat.div(n, 2n), e), L.Nat.div2_mono(n))
      L.Nat.le_min(Nat.min(V.View.so(), d1), V.View.so(), d2, L.Nat.min_le_l(V.View.so(), d1), L.Nat.le_trans(Nat.min(V.View.so(), d1), d1, d2, L.Nat.min_le_r(V.View.so(), d1), m))

# above and below together fit the window: (h - 1) / 2 + so_dn(h) <= h - 1
def Fit.half_dn(h: Nat) -> L.LE(Nat.add(Nat.div(Nat.sub(h, 1n), 2n), V.View.so_dn(h)), Nat.sub(h, 1n)):
  match h:
    case 0n:
      {==}
    case 1n++n:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, L.Nat.sub_zero(n)) : L.LE(Nat.add(Nat.div(_, 2n), V.View.so_dn(1n+n)), _)
      L.Nat.le_trans(Nat.add(Nat.div(n, 2n), V.View.so_dn(1n+n)), Nat.add(Nat.div(n, 2n), Nat.div(1n+n, 2n)), n, L.Nat.le_add_mono(Nat.div(n, 2n), V.View.so_dn(1n+n), Nat.div(1n+n, 2n), L.Nat.min_le_r(V.View.so(), Nat.div(1n+n, 2n))), L.Nat.div2_pair(n))

# View.fit keeps the cursor's line in the band
def Fit.band(+top: Nat, +l: Nat, +h: Nat, +last: Nat, hl: L.LE(l, last)) -> Band(V.View.fit(top, l, h, last), Fin.lo(l, V.View.so_in(h)), Fin.hi(l, V.View.so_dn(h), last, h)):
  +so = V.View.so_in(h)
  +sd = V.View.so_dn(h)
  +half = Nat.div(Nat.sub(h, 1n), 2n)
  +lo = Fin.lo(l, so)
  +hi = Fin.hi(l, sd, last, h)
  +mid = Nat.min(Nat.sub(l, half), Nat.sub(last, Nat.min(last, Nat.sub(h, 1n))))
  +hilo = Fit.hilo(l, h, last, so, sd, half, Fit.so_half(h), Fit.half_dn(h))
  +bmid = Fit.mid(l, h, last, so, sd, half, hl, Fit.so_half(h), Fit.half_dn(h))
  +up_c = Nat.is_gt(Nat.sub(top, lo), half)
  +down_c = Nat.is_gt(Nat.sub(hi, top), half)
  +up = Bool.pick(Nat, up_c, mid, lo)
  +down = Bool.pick(Nat, down_c, mid, hi)
  Band.pick2(Nat.is_lt(lo, top), Nat.is_gt(hi, top), lo, hi, top, up, down, {==}, {==}, Band.pick(up_c, mid, lo, lo, hi, bmid, (hilo, L.Nat.le_refl(lo))), Band.pick(down_c, mid, hi, lo, hi, bmid, (L.Nat.le_refl(hi), hilo)))

# half a window of w columns is at least half of its columns less one
def Fit.half_le(w: Nat) -> L.LE(Nat.div(Nat.sub(w, 1n), 2n), Nat.div(w, 2n)):
  match w:
    case 0n:
      {==}
    case 1n++n:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, L.Nat.sub_zero(n)) : L.LE(Nat.div(_, 2n), Nat.div(1n+n, 2n))
      L.Nat.div2_mono(n)

# w / 2 + (w - 1) / 2 is at most w - 1
def Fit.half_w(w: Nat) -> L.LE(Nat.add(Nat.div(w, 2n), Nat.div(Nat.sub(w, 1n), 2n)), Nat.sub(w, 1n)):
  match w:
    case 0n:
      {==}
    case 1n++n:
      %Equal.sym(Nat, Nat.sub(n, 0n), n, L.Nat.sub_zero(n)) : L.LE(Nat.add(Nat.div(1n+n, 2n), Nat.div(_, 2n)), _)
      %L.Nat.add_comm(Nat.div(n, 2n), Nat.div(1n+n, 2n)) : L.LE(_, n)
      L.Nat.div2_pair(n)

# View.fit_side keeps the cursor's column in the band; a centered column
# c - w / 2 lies in it too
def Fit.side(+left: Nat, +c: Nat, +w: Nat, +last: Nat) -> Band(V.View.fit_side(left, c, w, last), Fin.lo(c, V.View.so_in(w)), Fin.hi(c, V.View.so_in(w), last, w)):
  +so = V.View.so_in(w)
  +half = Nat.div(Nat.sub(w, 1n), 2n)
  +hw = Nat.div(w, 2n)
  +lo = Fin.lo(c, so)
  +hi = Fin.hi(c, so, last, w)
  +mid = Nat.sub(c, hw)
  +a = Nat.min(so, Nat.sub(last, c))
  +b = Nat.min(so, c)
  +h2 = L.Nat.le_trans(Nat.add(half, so), Nat.add(half, half), Nat.sub(w, 1n), L.Nat.le_add_mono(half, so, half, Fit.so_half(w)), L.Nat.div2_twice(Nat.sub(w, 1n)))
  +hilo = Fit.hilo(c, w, last, so, so, half, Fit.so_half(w), h2)
  +ha = L.Nat.le_trans(a, so, half, L.Nat.min_le_l(so, Nat.sub(last, c)), Fit.so_half(w))
  +himid = Fit.hi_le(c, a, hw, w, L.Nat.le_trans(Nat.add(hw, a), Nat.add(hw, half), Nat.sub(w, 1n), L.Nat.le_add_mono(hw, a, half, ha), Fit.half_w(w)))
  +midlo = L.Nat.sub_anti(c, b, hw, L.Nat.le_trans(b, half, hw, L.Nat.le_trans(b, so, half, L.Nat.min_le_l(so, c), Fit.so_half(w)), Fit.half_le(w)))
  +bmid = {(himid, midlo) : Band(mid, lo, hi)}
  +back_c = Nat.is_gt(Nat.sub(left, lo), hw)
  +ahead_c = Nat.is_gt(Nat.sub(hi, left), hw)
  +back = Bool.pick(Nat, back_c, mid, lo)
  +ahead = Bool.pick(Nat, ahead_c, mid, hi)
  Band.pick2(Nat.is_lt(lo, left), Nat.is_gt(hi, left), lo, hi, left, back, ahead, {==}, {==}, Band.pick(back_c, mid, lo, lo, hi, bmid, (hilo, L.Nat.le_refl(lo))), Band.pick(ahead_c, mid, hi, lo, hi, bmid, (L.Nat.le_refl(hi), hilo)))

# Final
# -----

def And2(A: Data, B: Data) -> Data:
  Sigma<&2, &2, A, _ => B>

# a window over lines ls, rows x cols, with the cursor at (line, col) and
# first line and column (top, left): settled
def Final.at(+ls: List<&2, String>, +rows: Nat, +cols: Nat, +opts: T.Opts, +onfile: Bool, +line: Nat, +col: Nat, +top: Nat, +left: Nat) -> Data:
  +last = M.Move.last_line(ls)
  +h = V.View.text_rows(rows)
  +w = V.View.text_cols(cols, V.View.gutter(opts, B.Lines.len(ls), onfile, cols))
  +lc = M.Move.last_col(ls, line)
  And2(L.LE(3n, rows), And2(L.LE(12n, cols), And2(L.LE(line, last), And2(L.LE(col, lc), And2(Band(top, Fin.lo(line, V.View.so_in(h)), Fin.hi(line, V.View.so_dn(h), last, h)), Band(left, Fin.lo(col, V.View.so_in(w)), Fin.hi(col, V.View.so_in(w), lc, w)))))))

# the editor s is settled
def Final(+s: T.St) -> Data:
  +w = S.St.win(s)
  Final.at(C.St.lines(s), S.St.rows(s), S.St.cols(s), S.St.opts(s), C.St.on_file(s), C.St.line(s), C.St.col(s), S.Win.top(w), S.Win.left(w))

# what Win.settle makes of a window over lines ls
def Final.win(+ls: List<&2, String>, +rows: Nat, +cols: Nat, +opts: T.Opts, +onfile: Bool, +line: Nat, +col: Nat, +top: Nat, +left: Nat)
  -> Final.at(ls, Nat.max(rows, 3n), Nat.max(cols, 12n), opts, onfile, Nat.min(line, M.Move.last_line(ls)), Nat.min(col, M.Move.last_col(ls, Nat.min(line, M.Move.last_line(ls)))),
       V.View.fit(Nat.min(top, V.View.max_top(V.View.text_rows(Nat.max(rows, 3n)), M.Move.last_line(ls))), Nat.min(line, M.Move.last_line(ls)), V.View.text_rows(Nat.max(rows, 3n)), M.Move.last_line(ls)),
       V.View.fit_side(left, Nat.min(col, M.Move.last_col(ls, Nat.min(line, M.Move.last_line(ls)))), V.View.text_cols(Nat.max(cols, 12n), V.View.gutter(opts, B.Lines.len(ls), onfile, Nat.max(cols, 12n))), M.Move.last_col(ls, Nat.min(line, M.Move.last_line(ls))))):
  +last = M.Move.last_line(ls)
  +l = Nat.min(line, last)
  +lc = M.Move.last_col(ls, l)
  +c = Nat.min(col, lc)
  +h = V.View.text_rows(Nat.max(rows, 3n))
  +w = V.View.text_cols(Nat.max(cols, 12n), V.View.gutter(opts, B.Lines.len(ls), onfile, Nat.max(cols, 12n)))
  (L.Nat.le_max_r(rows, 3n), (L.Nat.le_max_r(cols, 12n), (L.Nat.min_le_r(line, last), (L.Nat.min_le_r(col, lc), (Fit.band(Nat.min(top, V.View.max_top(h, last)), l, h, last, L.Nat.min_le_r(line, last)), Fit.side(left, c, w, lc))))))

# every editor Vim.fit gives is settled
def Final.of_fit(+x: T.St) -> Final(Vim.Vim.fit(x)):
  match x:
    case T.St{+files, +folded, +dirs, +win, +marks, +spots, +opened, +bufs, +back, +fwd, +mode, +count, +pend, +find, +hl, +opts, +rows, +cols, +msg, +stat}:
      match win:
        case T.Win{+tgt, +cur, +want, +top, +left}:
          match tgt:
            case T.File{+i}:
              match cur:
                case T.Pos{+line, +col}:
                  Final.win(B.Lines.some(B.Buf.lines(B.Files.at(files, i))), rows, cols, opts, True{}, line, col, top, left)
            case T.Dir{+path}:
              match cur:
                case T.Pos{+line, +col}:
                  Final.win(B.Lines.some(Maybe.default(&2, List<&2, String>, C.Listing.find(dirs, path), B.Oil.list(files, path))), rows, cols, opts, False{}, line, col, top, left)

# every editor Vim.final gives is settled
def Final.of(+x: T.St) -> Final(Vim.Vim.final(x)):
  +x2 = S.St.set_count(S.St.set_pend(x, Vim.Vim.pend(S.St.mode(x), S.St.pend(x))), Vim.Vim.count(S.St.mode(x), S.St.count(x)))
  Final.of_fit(S.St.set_win(x2, Vim.Vim.real(S.St.files(x), S.St.win(x))))
